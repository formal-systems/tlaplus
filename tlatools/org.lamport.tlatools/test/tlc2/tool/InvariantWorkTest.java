package tlc2.tool;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Proxy;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.OpDeclNode;
import tlc2.output.EC;
import tlc2.tool.impl.Tool.Mode;
import util.UniqueString;

public class InvariantWorkTest {

	@Rule
	public final TemporaryFolder tmp = new TemporaryFolder();

	private static final class RunResult {
		final int exitCode;
		final String output;

		RunResult(final int exitCode, final String output) {
			this.exitCode = exitCode;
			this.output = output;
		}
	}

	private Path writeSpec(final String name, final String tla, final String cfg) throws IOException {
		final Path dir = tmp.newFolder(name).toPath();
		Files.write(dir.resolve(name + ".tla"), tla.getBytes(StandardCharsets.UTF_8));
		Files.write(dir.resolve(name + ".cfg"), cfg.getBytes(StandardCharsets.UTF_8));
		return dir;
	}

	private static String absoluteClasspath() {
		final String sep = java.io.File.pathSeparator;
		final String[] entries = System.getProperty("java.class.path").split(Pattern.quote(sep));
		final StringBuilder sb = new StringBuilder();
		for (final String e : entries) {
			if (e.isEmpty()) {
				continue;
			}
			if (sb.length() > 0) {
				sb.append(sep);
			}
			sb.append(Path.of(e).toAbsolutePath().normalize());
		}
		return sb.toString();
	}

	private RunResult runTlc(final Path dir, final String specName, final List<String> jvmProps,
			final String... tlcArgs) throws Exception {
		final List<String> cmd = new ArrayList<>();
		cmd.add(Path.of(System.getProperty("java.home"), "bin", "java").toString());
		cmd.add("-ea");
		cmd.add("-XX:+UseParallelGC");
		cmd.add("-cp");
		cmd.add(absoluteClasspath());
		cmd.addAll(jvmProps);
		cmd.add("tlc2.TLC");
		cmd.add("-deadlock");
		cmd.add("-workers");
		cmd.add("1");
		cmd.add("-cleanup");
		cmd.add("-metadir");
		cmd.add(dir.resolve("states").toString());
		cmd.addAll(Arrays.asList(tlcArgs));
		cmd.add(specName);

		final ProcessBuilder pb = new ProcessBuilder(cmd);
		pb.directory(dir.toFile());
		pb.redirectErrorStream(true);
		final Process p = pb.start();
		final ByteArrayOutputStream baos = new ByteArrayOutputStream();
		try (InputStream in = p.getInputStream()) {
			final byte[] buf = new byte[4096];
			int n;
			while ((n = in.read(buf)) >= 0) {
				baos.write(buf, 0, n);
			}
		}
		final int code = p.waitFor();
		return new RunResult(code, baos.toString(StandardCharsets.UTF_8));
	}

	private static List<String> reportProp() {
		return Collections.singletonList("-D" + InvariantWork.INVARIANT_SKIP_REPORT + "=true");
	}

	@Test
	public void testSkipAndSilentByDefault() throws Exception {
		final String tla = ""
			+ "---- MODULE BasicSkip ----\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES x, y\n"
			+ "Init == x = 0 /\\ y = 0\n"
			+ "Next == (x < 3 /\\ x' = x + 1 /\\ UNCHANGED y)\n"
			+ "     \\/ (y < 4 /\\ y' = y + 1 /\\ UNCHANGED x)\n"
			+ "InvX == x >= 0\n"
			+ "InvY == y >= 0\n"
			+ "InvBoth == x + y >= 0\n"
			+ "====\n";
		final String cfg = ""
			+ "INIT Init\n"
			+ "NEXT Next\n"
			+ "INVARIANT InvX\n"
			+ "INVARIANT InvY\n"
			+ "INVARIANT InvBoth\n";
		final Path dir = writeSpec("BasicSkip", tla, cfg);

		// Default: silent (no invwork: lines), both normal and -tool mode
		final RunResult def = runTlc(dir, "BasicSkip", Collections.emptyList());
		assertEquals(def.output, EC.ExitStatus.SUCCESS, def.exitCode);
		assertFalse("Expected no invwork: output by default:\n" + def.output, def.output.contains("invwork:"));

		final RunResult toolRes = runTlc(dir, "BasicSkip", Collections.emptyList(), "-tool");
		assertEquals(toolRes.output, EC.ExitStatus.SUCCESS, toolRes.exitCode);
		assertFalse("Expected no invwork: output under -tool by default:\n" + toolRes.output,
				toolRes.output.contains("invwork:"));

		// Opt-in report property enables invwork: lines and confirms skipping happened
		final RunResult rep = runTlc(dir, "BasicSkip", reportProp());
		assertEquals(rep.output, EC.ExitStatus.SUCCESS, rep.exitCode);
		assertTrue(rep.output, rep.output.contains("invwork: invariant skip: InvX reads x"));
		assertTrue(rep.output, rep.output.contains("invwork: invariant skip: InvY reads y"));
		assertTrue(rep.output, rep.output.contains("invwork: invariant skip: InvBoth reads x, y"));
		assertTrue(rep.output, rep.output.contains("invwork: invariant InvX: evaluated 3, skipped 16"));
		assertTrue(rep.output, rep.output.contains("invwork: invariant InvY: evaluated 16, skipped 3"));
		assertTrue(rep.output, rep.output.contains("invwork: invariant InvBoth: evaluated 19, skipped 0"));

		// Explicit disable via system property
		final RunResult off = runTlc(dir, "BasicSkip", Arrays.asList(
				"-D" + InvariantWork.INVARIANT_SKIP + "=false",
				"-D" + InvariantWork.INVARIANT_SKIP_REPORT + "=true"));
		assertEquals(off.output, EC.ExitStatus.SUCCESS, off.exitCode);
		assertFalse("Expected no invwork: output when invariantSkip=false:\n" + off.output,
				off.output.contains("invwork:"));
	}

	@Test
	public void testImpureConstantFoldedFcnLambdaNotSkipped() throws Exception {
		// SpecProcessor constant-folds 0-arity ConstantLevel definitions into a lazy
		// FcnLambdaValue over Nat. Impure TLC overrides inside the body must mark the
		// invariant ALL instead of skipping it when x is unchanged.
		final String tla = ""
			+ "---- MODULE ImpureFcnLambda ----\n"
			+ "EXTENDS Naturals, TLC\n"
			+ "VARIABLES x, y\n"
			+ "F == [n \\in Nat |-> TLCSet(1, TLCGet(1) + 1) /\\ TLCGet(1) < 3]\n"
			+ "Init == TLCSet(1, 0) /\\ x = 0 /\\ y = 0\n"
			+ "Next == y < 5 /\\ y' = y + 1 /\\ UNCHANGED x\n"
			+ "Inv == F[x]\n"
			+ "====\n";
		final String cfg = ""
			+ "INIT Init\n"
			+ "NEXT Next\n"
			+ "INVARIANT Inv\n";
		final Path dir = writeSpec("ImpureFcnLambda", tla, cfg);

		final RunResult res = runTlc(dir, "ImpureFcnLambda", reportProp());
		assertEquals("Expected invariant violation when impure FcnLambdaValue runs:\n" + res.output,
				EC.ExitStatus.VIOLATION_SAFETY, res.exitCode);
		assertTrue(res.output, res.output.contains("invwork: invariant skip: Inv reads ALL"));
	}

	@Test
	public void testImpureConstantFoldedSetPredNotSkipped() throws Exception {
		final String tla = ""
			+ "---- MODULE ImpureSetPred ----\n"
			+ "EXTENDS Naturals, TLC\n"
			+ "VARIABLES x, y\n"
			+ "S == {n \\in Nat : TLCSet(2, TLCGet(2) + 1) /\\ TLCGet(2) < 3}\n"
			+ "Init == TLCSet(2, 0) /\\ x = 0 /\\ y = 0\n"
			+ "Next == y < 5 /\\ y' = y + 1 /\\ UNCHANGED x\n"
			+ "Inv == x \\in S\n"
			+ "====\n";
		final String cfg = ""
			+ "INIT Init\n"
			+ "NEXT Next\n"
			+ "INVARIANT Inv\n";
		final Path dir = writeSpec("ImpureSetPred", tla, cfg);

		final RunResult res = runTlc(dir, "ImpureSetPred", reportProp());
		assertEquals("Expected invariant violation when impure SetPredValue runs:\n" + res.output,
				EC.ExitStatus.VIOLATION_SAFETY, res.exitCode);
		assertTrue(res.output, res.output.contains("invwork: invariant skip: Inv reads ALL"));
	}

	@Test
	public void testImpureNestedInCompoundValueNotSkipped() throws Exception {
		final String tla = ""
			+ "---- MODULE ImpureCompound ----\n"
			+ "EXTENDS Naturals, TLC\n"
			+ "VARIABLES x, y\n"
			+ "R == [fn |-> [n \\in Nat |-> TLCSet(3, TLCGet(3) + 1) /\\ TLCGet(3) < 3]]\n"
			+ "Init == TLCSet(3, 0) /\\ x = 0 /\\ y = 0\n"
			+ "Next == y < 5 /\\ y' = y + 1 /\\ UNCHANGED x\n"
			+ "Inv == R.fn[x]\n"
			+ "====\n";
		final String cfg = ""
			+ "INIT Init\n"
			+ "NEXT Next\n"
			+ "INVARIANT Inv\n";
		final Path dir = writeSpec("ImpureCompound", tla, cfg);

		final RunResult res = runTlc(dir, "ImpureCompound", reportProp());
		assertEquals("Expected invariant violation when impure FcnLambdaValue is nested in RecordValue:\n" + res.output,
				EC.ExitStatus.VIOLATION_SAFETY, res.exitCode);
		assertTrue(res.output, res.output.contains("invwork: invariant skip: Inv reads ALL"));
	}

	@Test
	public void testPureConstantFoldedFcnLambdaStillSkips() throws Exception {
		final String tla = ""
			+ "---- MODULE PureFcnLambda ----\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES x, y\n"
			+ "PureF == [n \\in Nat |-> n >= 0]\n"
			+ "Init == x = 0 /\\ y = 0\n"
			+ "Next == y < 5 /\\ y' = y + 1 /\\ UNCHANGED x\n"
			+ "Inv == PureF[x]\n"
			+ "====\n";
		final String cfg = ""
			+ "INIT Init\n"
			+ "NEXT Next\n"
			+ "INVARIANT Inv\n";
		final Path dir = writeSpec("PureFcnLambda", tla, cfg);

		final RunResult res = runTlc(dir, "PureFcnLambda", reportProp());
		assertEquals(res.output, EC.ExitStatus.SUCCESS, res.exitCode);
		assertTrue(res.output, res.output.contains("invwork: invariant skip: Inv reads x"));
		assertTrue(res.output, res.output.contains("invwork: invariant Inv: evaluated 0, skipped 5"));
	}

	@Test
	public void testCoverageDisablesSkipAndPreservesCounts() throws Exception {
		final String tla = ""
			+ "---- MODULE CovSkip ----\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES x, y\n"
			+ "Init == x = 0 /\\ y = 0\n"
			+ "Next == y < 10 /\\ y' = y + 1 /\\ UNCHANGED x\n"
			+ "InvX == x >= 0\n"
			+ "====\n";
		final String cfg = ""
			+ "INIT Init\n"
			+ "NEXT Next\n"
			+ "INVARIANT InvX\n";
		final Path dir = writeSpec("CovSkip", tla, cfg);

		final RunResult withDefault = runTlc(dir, "CovSkip", reportProp(), "-coverage", "1");
		assertEquals(withDefault.output, EC.ExitStatus.SUCCESS, withDefault.exitCode);
		assertTrue(withDefault.output, withDefault.output.contains("invwork: invariant skip off: -coverage"));

		final RunResult withSkipOff = runTlc(dir, "CovSkip",
				Collections.singletonList("-D" + InvariantWork.INVARIANT_SKIP + "=false"),
				"-coverage", "1");
		assertEquals(withSkipOff.output, EC.ExitStatus.SUCCESS, withSkipOff.exitCode);

		final Pattern p = Pattern.compile("<InvX [^>]+>\\R\\s+line 6, col \\d+ to line 6, col \\d+ of module CovSkip: (\\d+)");
		final Matcher m1 = p.matcher(withDefault.output);
		final Matcher m2 = p.matcher(withSkipOff.output);
		assertTrue("InvX coverage line not found:\n" + withDefault.output, m1.find());
		assertTrue("InvX coverage line not found (skip off):\n" + withSkipOff.output, m2.find());
		assertEquals("11", m1.group(1));
		assertEquals(m2.group(1), m1.group(1));
	}

	@Test
	public void testContinueDisablesSkip() throws Exception {
		final String tla = ""
			+ "---- MODULE ContSkip ----\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES x, y\n"
			+ "Init == x = 0 /\\ y = 0\n"
			+ "Next == y < 3 /\\ y' = y + 1 /\\ UNCHANGED x\n"
			+ "InvX == x >= 0\n"
			+ "====\n";
		final String cfg = ""
			+ "INIT Init\n"
			+ "NEXT Next\n"
			+ "INVARIANT InvX\n";
		final Path dir = writeSpec("ContSkip", tla, cfg);

		final RunResult res = runTlc(dir, "ContSkip", reportProp(), "-continue");
		assertEquals(res.output, EC.ExitStatus.SUCCESS, res.exitCode);
		assertTrue(res.output, res.output.contains("invwork: invariant skip off: -continue"));
	}

	@Test
	public void testInstanceCfgOverrideRecursiveAndLambda() throws Exception {
		final Path dir = tmp.newFolder("ComplexConstructs").toPath();
		final String sub = ""
			+ "---- MODULE SubMod ----\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLE u\n"
			+ "SubInv == u < 3\n"
			+ "====\n";
		final String main = ""
			+ "---- MODULE MainMod ----\n"
			+ "EXTENDS Naturals, Sequences\n"
			+ "VARIABLES x, y, z\n"
			+ "Limit == 0\n"
			+ "M == INSTANCE SubMod WITH u <- y\n"
			+ "RECURSIVE SumTo(_)\n"
			+ "SumTo(n) == IF n = 0 THEN 0 ELSE n + SumTo(n - 1)\n"
			+ "Init == x = 0 /\\ y = 0 /\\ z = 0\n"
			+ "Next == (y < 4 /\\ y' = y + 1 /\\ UNCHANGED <<x, z>>)\n"
			+ "     \\/ (z < 2 /\\ z' = z + 1 /\\ UNCHANGED <<x, y>>)\n"
			+ "InvInst == M!SubInv\n"
			+ "InvCfg == x <= Limit\n"
			+ "InvRec == SumTo(z) >= 0\n"
			+ "InvLambda == Len(SelectSeq(<<1, 2, 3>>, LAMBDA e : e > z)) >= 0\n"
			+ "LimitState == y\n"
			+ "====\n";
		final String cfg = ""
			+ "INIT Init\n"
			+ "NEXT Next\n"
			+ "CONSTANT Limit <- LimitState\n"
			+ "INVARIANT InvInst\n"
			+ "INVARIANT InvCfg\n"
			+ "INVARIANT InvRec\n"
			+ "INVARIANT InvLambda\n";
		Files.write(dir.resolve("SubMod.tla"), sub.getBytes(StandardCharsets.UTF_8));
		Files.write(dir.resolve("MainMod.tla"), main.getBytes(StandardCharsets.UTF_8));
		Files.write(dir.resolve("MainMod.cfg"), cfg.getBytes(StandardCharsets.UTF_8));

		final RunResult res = runTlc(dir, "MainMod", reportProp());
		// InvInst fails when y reaches 3
		assertEquals(res.output, EC.ExitStatus.VIOLATION_SAFETY, res.exitCode);
		assertTrue(res.output, res.output.contains("invwork: invariant skip: InvInst reads y"));
		assertTrue(res.output, res.output.contains("invwork: invariant skip: InvCfg reads x, y"));
		assertTrue(res.output, res.output.contains("invwork: invariant skip: InvRec reads z"));
		assertTrue(res.output, res.output.contains("invwork: invariant skip: InvLambda reads z"));
	}

	@Test
	public void testMoreThan64Variables() throws Exception {
		final int n = 70;
		final StringBuilder varDecl = new StringBuilder();
		final StringBuilder initBody = new StringBuilder();
		final StringBuilder unchangedExcept0 = new StringBuilder();
		final StringBuilder unchangedExcept68 = new StringBuilder();
		for (int i = 0; i < n; i++) {
			if (i > 0) {
				varDecl.append(", ");
				initBody.append(" /\\ ");
			}
			varDecl.append("v").append(i);
			initBody.append("v").append(i).append(" = 0");
			if (i != 0) {
				if (unchangedExcept0.length() > 0) {
					unchangedExcept0.append(", ");
				}
				unchangedExcept0.append("v").append(i);
			}
			if (i != 68) {
				if (unchangedExcept68.length() > 0) {
					unchangedExcept68.append(", ");
				}
				unchangedExcept68.append("v").append(i);
			}
		}

		final String tla = ""
			+ "---- MODULE ManyVars ----\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES " + varDecl + "\n"
			+ "Init == " + initBody + "\n"
			+ "Next == (v0 < 5 /\\ v0' = v0 + 1 /\\ UNCHANGED <<" + unchangedExcept0 + ">>)\n"
			+ "     \\/ (v0 = 5 /\\ v68 = 0 /\\ v68' = 1 /\\ UNCHANGED <<" + unchangedExcept68 + ">>)\n"
			+ "InvHi == v68 = 0\n"
			+ "====\n";
		final String cfg = ""
			+ "INIT Init\n"
			+ "NEXT Next\n"
			+ "INVARIANT InvHi\n";
		final Path dir = writeSpec("ManyVars", tla, cfg);

		final RunResult res = runTlc(dir, "ManyVars", reportProp());
		assertEquals("Expected InvHi violation when v68 changes in second mask word:\n" + res.output,
				EC.ExitStatus.VIOLATION_SAFETY, res.exitCode);
		assertTrue(res.output, res.output.contains("invwork: invariant skip: InvHi reads v68"));
		assertTrue(res.output, res.output.contains("invwork: invariant InvHi: evaluated 1, skipped 5"));
	}

	@Test
	public void testRecoveringDisablesSkip() {
		final OpDeclNode[] savedVars = TLCState.vars;
		try {
			UniqueString.setVariableCount(1);
			final UniqueString vx = UniqueString.uniqueStringOf("recoverTest_x");
			vx.setLoc(0);
			TLCState.vars = new OpDeclNode[] {
				new OpDeclNode(vx, ASTConstants.VariableDeclKind, 1, 0, null, null, null)
			};
			final ITool stubTool = (ITool) Proxy.newProxyInstance(
				ITool.class.getClassLoader(),
				new Class<?>[] { ITool.class },
				(proxy, method, args) -> {
					switch (method.getName()) {
					case "getInvariants":
						return new Action[] { new Action(null, null) };
					case "getInvNames":
						return new String[] { "Inv" };
					case "getMode":
						return Mode.MC;
					default:
						return null;
					}
				});
			assertNull("InvariantWork must be disabled when recovering from a checkpoint",
					InvariantWork.create(stubTool, true));
		} finally {
			TLCState.vars = savedVars;
		}
	}
}
