// Copyright (c) 2026, Oracle and/or its affiliates.
package tlc2.tool;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

import tla2sany.semantic.APSubstInNode;
import tla2sany.semantic.AtNode;
import tla2sany.semantic.DecimalNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tlc2.util.Context;
import tlc2.value.impl.EvaluatingValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.MethodValue;
import tlc2.value.impl.OpValue;
import tlc2.value.impl.Value;

/**
 * F2 invariant skip ({@link InvariantWork}): a static over-approximation of the state variables an
 * invariant reads. The walk resolves every operator as the evaluator does ({@link ITool#lookup},
 * so cfg substitutions {@code <-} and constant overrides are followed), and takes the union of an
 * operator's body and of its arguments (operator arguments and LAMBDAs included), so the result
 * does not depend on the calling context and is memoized per {@link OpDefNode}; INSTANCE
 * substitutions add the variables of their right-hand sides, RECURSIVE definitions are handled by
 * a cycle guard (results inside a cycle are memoized only at the cycle's entry).
 * <p>
 * The result is ALL (no skip) for anything the walk cannot vouch for:
 * <ul>
 * <li><b>state-level ALL</b>: ENABLED, primes, action and temporal operators (they do not
 * belong in an invariant);</li>
 * <li><b>impure ALL</b>: a Java override outside the whitelist of pure standard operators
 * ({@link #PURE_CLASSES}, {@link #PURE_TLC}), e.g. TLCGet, TLCSet, Print, PrintT, RandomElement,
 * JavaTime, Any, TLCExt, IOUtils, CSV and user overrides, any other operator value, and any node
 * or tool object the walk does not know. Such an invariant may depend on more than the state.</li>
 * </ul>
 */
public final class InvariantReads {

	/** Java overrides from these classes are pure functions of their arguments. */
	static final Set<String> PURE_CLASSES = Set.of("tlc2.module.Naturals", "tlc2.module.Integers",
			"tlc2.module.Sequences", "tlc2.module.FiniteSets", "tlc2.module.Bags", "tlc2.module.TLCEval");
	/** The pure part of tlc2.module.TLC: :>, @@, Permutations, SortSeq, ToString, Assert. */
	static final Set<String> PURE_TLC = Set.of("MakeFcn", "CombineFcn", "Permutations", "SortSeq", "ToString",
			"Assert");
	static final String TLC_CLASS = "tlc2.module.TLC";

	/** The variables one expression (an invariant) reads. */
	public static final class Reads {
		/** The variable locations read; meaningful only if {@link #all} is null. */
		public final BitSet vars;
		/** Null, or why the invariant gets ALL (the first reason found). */
		public final String all;
		/** Null, or why the invariant may depend on more than the state (implies all != null). */
		public final String impure;

		Reads(final BitSet vars, final String all, final String impure) {
			this.vars = vars;
			this.all = all;
			this.impure = impure;
		}

		public boolean isAll() {
			return this.all != null;
		}
	}

	/** The accumulator of one walk (an invariant, or one definition's body). */
	private static final class Acc {
		final BitSet vars = new BitSet();
		String all;
		String impure;
		/** The lowest stack index of a definition in progress that this walk reached. */
		int low = Integer.MAX_VALUE;

		void setAll(final String why) {
			if (this.all == null) {
				this.all = why;
			}
		}

		void setImpure(final String why) {
			setAll(why);
			if (this.impure == null) {
				this.impure = why;
			}
		}

		void merge(final Reads r) {
			this.vars.or(r.vars);
			if (r.all != null) {
				setAll(r.all);
			}
			if (r.impure != null) {
				setImpure(r.impure);
			}
		}

		Reads toReads() {
			return new Reads(this.vars, this.all, this.impure);
		}
	}

	private final ITool tool;
	private final int varCount;
	private final Map<OpDefNode, Reads> memo = new IdentityHashMap<>();
	private final Map<OpDefNode, Integer> onStack = new IdentityHashMap<>();
	private final ArrayList<OpDefNode> stack = new ArrayList<>();

	public InvariantReads(final ITool tool, final int varCount) {
		this.tool = tool;
		this.varCount = varCount;
	}

	/** The variables the invariant (an Action: pred in con) reads. */
	public Reads of(final Action inv) {
		final Acc acc = new Acc();
		walkContext(inv.con, acc, 0);
		walk(inv.pred, acc);
		return acc.toReads();
	}

	/** The variables the expression reads (for tests). */
	public Reads of(final SemanticNode expr) {
		final Acc acc = new Acc();
		walk(expr, acc);
		return acc.toReads();
	}

	/** A context's values are what its names stand for in pred: they are walked as well. */
	private void walkContext(Context c, final Acc acc, final int depth) {
		if (depth > 64) {
			acc.setImpure("context too deep");
			return;
		}
		while (c != null && !c.isEmpty()) {
			final Object v = c.getValue();
			if (v != null) {
				walkObject(v, acc, "a context value", depth);
			}
			c = c.next();
		}
	}

	private void walkObject(final Object v, final Acc acc, final String what, final int depth) {
		if (v instanceof LazyValue) {
			final LazyValue lv = (LazyValue) v;
			walkContext(lv.con, acc, depth + 1);
			walk(lv.expr, acc);
		} else if (v instanceof OpDefNode) {
			walkDef((OpDefNode) v, acc);
		} else if (v instanceof OpValue) {
			checkOverride((OpValue) v, acc, what);
		} else if (v instanceof Value) {
			// a constant
		} else if (v instanceof SemanticNode) {
			walk((SemanticNode) v, acc);
		} else {
			acc.setImpure("unexpected object " + v.getClass().getName() + " for " + what);
		}
	}

	private void walk(final SemanticNode n, final Acc acc) {
		if (n == null) {
			return;
		}
		if (n instanceof OpApplNode) {
			walkAppl((OpApplNode) n, acc);
		} else if (n instanceof LetInNode) {
			// The LET definitions are walked where they are used (their OpApplNodes resolve to them).
			walk(((LetInNode) n).getBody(), acc);
		} else if (n instanceof SubstInNode) {
			final SubstInNode s = (SubstInNode) n;
			walkSubsts(s.getSubsts(), acc);
			walk(s.getBody(), acc);
		} else if (n instanceof APSubstInNode) {
			final APSubstInNode s = (APSubstInNode) n;
			walkSubsts(s.getSubsts(), acc);
			walk(s.getBody(), acc);
		} else if (n instanceof LabelNode) {
			walk(((LabelNode) n).getBody(), acc);
		} else if (n instanceof OpArgNode) {
			resolve(((OpArgNode) n).getOp(), acc);
		} else if (n instanceof NumeralNode || n instanceof StringNode || n instanceof DecimalNode
				|| n instanceof AtNode) {
			// A literal; @ is the value of the EXCEPT's function, which is walked as its argument.
		} else {
			acc.setImpure("expression kind " + n.getClass().getSimpleName());
		}
	}

	private void walkSubsts(final Subst[] subs, final Acc acc) {
		for (int i = 0; i < subs.length; i++) {
			walk(subs[i].getExpr(), acc);
		}
	}

	private void walkAppl(final OpApplNode e, final Acc acc) {
		final ExprOrOpArgNode[] args = e.getArgs();
		if (args != null) {
			for (int i = 0; i < args.length; i++) {
				walk(args[i], acc);
			}
		}
		final ExprNode[] bnds = e.getBdedQuantBounds();
		if (bnds != null) {
			for (int i = 0; i < bnds.length; i++) {
				walk(bnds[i], acc);
			}
		}
		final SymbolNode op = e.getOperator();
		final int opcode = BuiltInOPs.getOpCode(op.getName());
		if (opcode != 0) {
			builtin(opcode, op, acc);
		} else {
			resolve(op, acc);
		}
	}

	private static void builtin(final int opcode, final SymbolNode op, final Acc acc) {
		if (opcode == ToolGlobals.OPCODE_enabled || opcode >= ToolGlobals.OPCODE_prime) {
			acc.setAll("action or temporal operator " + op.getName());
		}
	}

	/** An operator symbol, as Spec#lookup(opNode, c, s, cutoff) resolves it outside any context. */
	private void resolve(final SymbolNode op, final Acc acc) {
		final Object val = this.tool.lookup(op, Context.Empty, false);
		if (val instanceof OpDefNode) {
			final OpDefNode def = (OpDefNode) val;
			final int opcode = BuiltInOPs.getOpCode(def.getName());
			if (opcode != 0) {
				builtin(opcode, def, acc); // substituted by a built-in operator
			} else {
				walkDef(def, acc);
			}
		} else if (val instanceof ThmOrAssumpDefNode) {
			walk(((ThmOrAssumpDefNode) val).getBody(), acc);
		} else if (val instanceof OpValue) {
			checkOverride((OpValue) val, acc, op.getName().toString());
		} else if (val instanceof LazyValue) {
			walkObject(val, acc, op.getName().toString(), 0);
		} else if (val instanceof Value) {
			// a constant (a CONSTANT's value, or a constant definition evaluated at startup)
		} else if (val == op) {
			// A declaration that resolves to itself: the evaluator reads the state variable of its
			// name (a VARIABLE, or a parameter of an instantiated module whose substitution was
			// walked at the SubstInNode). A formal parameter is always bound in the context, its
			// actual argument is walked at the call.
			if (!(op instanceof FormalParamNode)) {
				final int loc = op.getName().getVarLoc();
				if (loc >= 0 && loc < this.varCount) {
					acc.vars.set(loc);
				} else if (!(op instanceof OpDeclNode)) {
					acc.setImpure("unresolved operator " + op.getName());
				}
			}
		} else {
			acc.setImpure("unexpected tool object " + (val == null ? "null" : val.getClass().getName()) + " for "
					+ op.getName());
		}
	}

	private static void checkOverride(final OpValue val, final Acc acc, final String name) {
		final Method m;
		if (val.getClass() == MethodValue.class) {
			m = ((MethodValue) val).getMethod();
		} else if (val.getClass() == EvaluatingValue.class) {
			m = ((EvaluatingValue) val).getMethod();
		} else {
			acc.setImpure("operator value " + val.getClass().getSimpleName() + " for " + name);
			return;
		}
		final String cls = m.getDeclaringClass().getName();
		if (PURE_CLASSES.contains(cls) || (TLC_CLASS.equals(cls) && PURE_TLC.contains(m.getName()))) {
			return;
		}
		acc.setImpure("Java override " + cls + "." + m.getName() + " for " + name);
	}

	private void walkDef(final OpDefNode def, final Acc acc) {
		final Reads done = this.memo.get(def);
		if (done != null) {
			acc.merge(done);
			return;
		}
		final Integer idx = this.onStack.get(def);
		if (idx != null) {
			// RECURSIVE: what def reads is added where its walk completes.
			acc.low = Math.min(acc.low, idx);
			return;
		}
		final ExprNode body = def.getBody();
		if (body == null) {
			acc.setImpure("no definition for " + def.getName());
			return;
		}
		final int me = this.stack.size();
		this.stack.add(def);
		this.onStack.put(def, me);
		final Acc sub = new Acc();
		try {
			walk(body, sub);
		} finally {
			this.stack.remove(me);
			this.onStack.remove(def);
		}
		if (sub.low >= me) {
			// Complete: no definition below me on the stack was reached (a cycle back to me is
			// complete once I am).
			sub.low = Integer.MAX_VALUE;
			this.memo.put(def, sub.toReads());
		}
		acc.merge(sub.toReads());
		if (sub.low < me) {
			acc.low = Math.min(acc.low, sub.low);
		}
	}
}
