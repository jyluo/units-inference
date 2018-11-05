package units;

import checkers.inference.test.CFInferenceTest;
import java.io.File;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.framework.test.TestUtilities;
import org.checkerframework.javacutil.Pair;
import org.junit.runners.Parameterized.Parameters;
import units.solvers.backend.UnitsSolverEngine;

public class UnitsInferenceTest extends CFInferenceTest {

    public UnitsInferenceTest(File testFile) {
        super(
                testFile,
                units.UnitsChecker.class,
                "units",
                "-Anomsgtext",
                "-d",
                "tests/build/outputdir");
    }

    @Override
    public boolean useHacks() {
        return true;
    }

    @Override
    public Pair<String, List<String>> getSolverNameAndOptions() {
        final String solverName = UnitsSolverEngine.class.getCanonicalName();
        List<String> solverOptions = new ArrayList<>();
        solverOptions.add("solver=Z3smt");
        return Pair.<String, List<String>>of(solverName, solverOptions);
    }

    @Parameters
    public static List<File> getTestFiles() {
        List<File> testfiles = new ArrayList<>();
        testfiles.addAll(TestUtilities.findRelativeNestedJavaFiles("testing", "inference"));
        return testfiles;
    }
}
