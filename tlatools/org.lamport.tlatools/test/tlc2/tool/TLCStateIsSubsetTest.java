package tlc2.tool;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.fail;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.OpDeclNode;
import tlc2.util.PartialBoolean;
import tlc2.value.IValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import util.UniqueString;

public class TLCStateIsSubsetTest {

	private OpDeclNode[] savedVars;
	private TLCState savedEmpty;

	private OpDeclNode[] vars;
	private UniqueString v0;
	private UniqueString v1;
	private UniqueString v2;

	@Before
	public void setUp() {
		savedVars = TLCState.vars;
		savedEmpty = TLCState.Empty;

		UniqueString.setVariableCount(3);
		v0 = UniqueString.uniqueStringOf("isSubsetTest_a");
		v1 = UniqueString.uniqueStringOf("isSubsetTest_b");
		v2 = UniqueString.uniqueStringOf("isSubsetTest_c");
		v0.setLoc(0);
		v1.setLoc(1);
		v2.setLoc(2);
		vars = new OpDeclNode[] {
			new OpDeclNode(v0, ASTConstants.VariableDeclKind, 1, 0, null, null, null),
			new OpDeclNode(v1, ASTConstants.VariableDeclKind, 1, 0, null, null, null),
			new OpDeclNode(v2, ASTConstants.VariableDeclKind, 1, 0, null, null, null),
		};
	}

	@After
	public void tearDown() {
		TLCState.vars = savedVars;
		TLCState.Empty = savedEmpty;
	}

	private TLCState newMut(final IValue a, final IValue b, final IValue c) {
		TLCStateMut.setVariables(vars);
		final TLCState s = TLCState.Empty.createEmpty();
		if (a != null) {
			s.bind(v0, a);
		}
		if (b != null) {
			s.bind(v1, b);
		}
		if (c != null) {
			s.bind(v2, c);
		}
		return s;
	}

	private TLCState newMutExt(final IValue a, final IValue b, final IValue c) {
		TLCStateMutExt.setVariables(vars);
		final TLCState s = TLCState.Empty.createEmpty();
		if (a != null) {
			s.bind(v0, a);
		}
		if (b != null) {
			s.bind(v1, b);
		}
		if (c != null) {
			s.bind(v2, c);
		}
		return s;
	}

	private TLCState newFun(final IValue a, final IValue b, final IValue c) {
		TLCState s = TLCStateFun.Empty;
		if (a != null) {
			s = s.bind(vars[0], a);
		}
		if (b != null) {
			s = s.bind(vars[1], b);
		}
		if (c != null) {
			s = s.bind(vars[2], c);
		}
		return s;
	}

	private static IValue tuple(final int x, final int y) {
		return new TupleValue(new tlc2.value.impl.Value[] { IntValue.gen(x), IntValue.gen(y) });
	}

	@Test
	public void testMutFastPath() {
		TLCStateMut.setVariables(vars);
		final TLCState sFull = newMut(IntValue.gen(1), tuple(2, 3), new StringValue("ok"));
		assertNotNull(sFull.valuesByLocation());

		// Null and Empty
		assertEquals(PartialBoolean.YES, TLCState.isSubset(sFull, null));
		assertEquals(PartialBoolean.YES, TLCState.isSubset(sFull, TLCState.Empty));
		assertEquals(PartialBoolean.YES, TLCState.isSubset(null, TLCState.Empty));
		assertEquals(PartialBoolean.NO, TLCState.isSubset(null, sFull));
		assertEquals(PartialBoolean.YES, TLCState.isSubset(null, newMut(null, null, null)));

		// Same reference
		assertEquals(PartialBoolean.YES, TLCState.isSubset(sFull, sFull));

		// Equal values (including distinct non-identical Value instances)
		final TLCState sEqual = newMut(IntValue.gen(1), tuple(2, 3), new StringValue("ok"));
		assertEquals(PartialBoolean.YES, TLCState.isSubset(sFull, sEqual));

		// Proper subset: s2 constrains fewer variables than s1
		final TLCState sPartial = newMut(IntValue.gen(1), null, new StringValue("ok"));
		assertEquals(PartialBoolean.YES, TLCState.isSubset(sFull, sPartial));
		assertEquals(PartialBoolean.NO, TLCState.isSubset(sPartial, sFull));

		// Different value
		final TLCState sDiff = newMut(IntValue.gen(1), tuple(2, 4), new StringValue("ok"));
		assertEquals(PartialBoolean.NO, TLCState.isSubset(sFull, sDiff));

		// Incomparable values (int vs string) -> MAYBE
		final TLCState sIncomp = newMut(new StringValue("not-int"), tuple(2, 3), new StringValue("ok"));
		assertEquals(PartialBoolean.MAYBE, TLCState.isSubset(sFull, sIncomp));

		// Slot 0 differs (NO) before slot 1 is incomparable (MAYBE) -> NO (same order as slow path)
		final TLCState sNoBeforeMaybe = newMut(IntValue.gen(99), new StringValue("not-tuple"), null);
		assertEquals(PartialBoolean.NO, TLCState.isSubset(sFull, sNoBeforeMaybe));
	}

	@Test
	public void testMutExtFastPathAndCrossType() {
		final TLCState mut = newMut(IntValue.gen(1), tuple(2, 3), new StringValue("x"));
		final TLCState ext = newMutExt(IntValue.gen(1), tuple(2, 3), null);
		final TLCState extDiff = newMutExt(IntValue.gen(1), tuple(2, 9), null);
		final TLCState extIncomp = newMutExt(new StringValue("s"), tuple(2, 3), null);

		assertNotNull(mut.valuesByLocation());
		assertNotNull(ext.valuesByLocation());

		assertEquals(PartialBoolean.YES, TLCState.isSubset(mut, ext));
		assertEquals(PartialBoolean.NO, TLCState.isSubset(ext, mut));
		assertEquals(PartialBoolean.NO, TLCState.isSubset(mut, extDiff));
		assertEquals(PartialBoolean.MAYBE, TLCState.isSubset(mut, extIncomp));
		assertEquals(PartialBoolean.YES, TLCState.isSubset(ext, ext));
		assertEquals(PartialBoolean.YES, TLCState.isSubset(ext, TLCState.Empty));
	}

	@Test
	public void testFastPathMatchesSlowPath() {
		final TLCState mut1 = newMut(IntValue.gen(1), tuple(2, 3), null);
		final TLCState fun1 = newFun(IntValue.gen(1), tuple(2, 3), null);
		assertNull(fun1.valuesByLocation());

		final IValue[][] candidates = new IValue[][] {
			{ null, null, null },
			{ IntValue.gen(1), null, null },
			{ IntValue.gen(1), tuple(2, 3), null },
			{ IntValue.gen(1), tuple(2, 3), IntValue.gen(4) },
			{ IntValue.gen(2), tuple(2, 3), null },
			{ new StringValue("x"), tuple(2, 3), null },
			{ IntValue.gen(2), new StringValue("x"), null },
			{ null, new StringValue("x"), null },
		};

		for (final IValue[] c : candidates) {
			final TLCState mut2 = newMut(c[0], c[1], c[2]);
			final TLCState fun2 = newFun(c[0], c[1], c[2]);
			final PartialBoolean fast = TLCState.isSubset(mut1, mut2);
			assertEquals(fast, TLCState.isSubset(fun1, fun2));
			assertEquals(fast, TLCState.isSubset(mut1, fun2));
			assertEquals(fast, TLCState.isSubset(fun1, mut2));
		}
	}

	@Test
	public void testSetVariablesAssertsVarLocInvariant() {
		if (!TLCStateMut.class.desiredAssertionStatus()) {
			return;
		}
		final OpDeclNode[] swapped = new OpDeclNode[] { vars[1], vars[0], vars[2] };
		try {
			TLCStateMut.setVariables(swapped);
			fail("Expected AssertionError for mismatched varLoc in TLCStateMut.setVariables");
		} catch (final AssertionError expected) {
			// expected
		}
		try {
			TLCStateMutExt.setVariables(swapped);
			fail("Expected AssertionError for mismatched varLoc in TLCStateMutExt.setVariables");
		} catch (final AssertionError expected) {
			// expected
		}
	}
}
