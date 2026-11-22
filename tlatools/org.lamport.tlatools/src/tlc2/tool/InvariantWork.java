// Copyright (c) 2026, Oracle and/or its affiliates.
package tlc2.tool;

import java.util.BitSet;
import java.util.stream.Collectors;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.impl.Tool.Mode;
import util.ToolIO;

/**
 * F2, invariant skip: less invariant work in the BFS model checker, with the same results. On by
 * default; {@code -Dtlc2.tool.Worker.invariantSkip=false} turns it off.
 * <p>
 * Invariant k is not evaluated in a successor that holds, for every variable k reads
 * ({@link InvariantReads}), the identical object as its parent. The parent passed every invariant
 * (without -continue only states that passed are enqueued), so k holds in the successor. Off under
 * -continue and in the debugger.
 * <p>
 * Only {@link Worker} (BFS) uses it: not the initial states, not the simulator, not DFID.
 */
public final class InvariantWork {

	public static final String INVARIANT_SKIP = Worker.class.getName() + ".invariantSkip";

	private static final String P = "invwork: ";

	/**
	 * One statistics line. With -tool every line TLC prints must be inside a message frame, so the
	 * line goes out as an EC.GENERAL message there; otherwise it is printed as is.
	 */
	private static void say(final String line) {
		if (TLCGlobals.tool) {
			MP.printMessage(EC.GENERAL, P + line);
		} else {
			ToolIO.out.println(P + line);
		}
	}

	/**
	 * Per invariant the bit mask (by variable location) of the variables it reads, or null for ALL
	 * (always evaluated).
	 */
	final long[][] masks;
	/** The locations read by some invariant whose mask is not ALL (the slots compared). */
	final int[] locs;
	/** The words of a mask. */
	final int words;
	final String[] names;

	private InvariantWork(final long[][] masks, final int[] locs, final int words, final String[] names) {
		this.masks = masks;
		this.locs = locs;
		this.words = words;
		this.names = names;
	}

	/** Null when off. Prints what is on, and why it is off. */
	static InvariantWork create(final ITool tool) {
		final boolean skip = Boolean.parseBoolean(System.getProperty(INVARIANT_SKIP, "true"));
		if (!skip) {
			return null;
		}
		final Action[] invs = tool.getInvariants();
		final String[] names = tool.getInvNames();
		final int varCount = TLCState.vars.length;

		String off = null;
		if (TLCGlobals.continuation) {
			off = "-continue"; // a parent may have failed an invariant
		} else if (tool.getMode() == Mode.MC_DEBUG) {
			off = "the debugger";
		} else if (invs.length == 0) {
			off = "no invariants";
		}
		if (off != null) {
			say("invariant skip off: " + off);
			return null;
		}

		// The static analysis, once.
		final InvariantReads analysis = new InvariantReads(tool, varCount);
		final int words = (varCount + 63) >>> 6;
		final long[][] masks = new long[invs.length][];
		final BitSet union = new BitSet();
		for (int k = 0; k < invs.length; k++) {
			final InvariantReads.Reads r = analysis.of(invs[k]);
			if (r.isAll()) {
				say("invariant skip: " + names[k] + " reads ALL (" + r.all + ")");
				continue;
			}
			final long[] m = new long[words];
			final long[] w = r.vars.toLongArray();
			System.arraycopy(w, 0, m, 0, Math.min(w.length, words));
			masks[k] = m;
			union.or(r.vars);
			say("invariant skip: " + names[k] + " reads " + varNames(r.vars));
		}
		final int[] locs = union.stream().toArray();
		say("invariant skip on: " + union.cardinality() + " of " + varCount
				+ " variables compared per successor");
		return new InvariantWork(masks, locs, words, names);
	}

	private static String varNames(final BitSet vars) {
		if (vars.isEmpty()) {
			return "no variable";
		}
		return vars.stream().mapToObj(i -> TLCState.vars[i].getName().toString())
				.collect(Collectors.joining(", "));
	}

	/** The end lines: per invariant, the evaluations done and skipped. */
	void report(final IWorker[] workers) {
		final long[] eval = new long[this.names.length], skipped = new long[this.names.length];
		for (final IWorker t : workers) {
			if (t instanceof Worker) {
				final Worker w = (Worker) t;
				for (int k = 0; k < eval.length; k++) {
					eval[k] += w.iwEval[k];
					skipped[k] += w.iwSkip[k];
				}
			}
		}
		for (int k = 0; k < eval.length; k++) {
			say("invariant " + this.names[k] + ": evaluated " + eval[k] + ", skipped " + skipped[k]
					+ (this.masks[k] == null ? " (ALL)" : ""));
		}
	}
}
