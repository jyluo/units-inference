package units;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.framework.test.CheckerFrameworkPerFileTest;
import org.checkerframework.framework.test.TestUtilities;
import org.junit.runners.Parameterized.Parameters;

public class UnitsTypecheckTest extends CheckerFrameworkPerFileTest {

    public UnitsTypecheckTest(File testFile) {
        super(testFile, units.UnitsChecker.class, "units", "-d", "tests/build/outputdir"
        // );
                , "-Anomsgtext"); // comment to show bugs
    }

    @Parameters
    public static List<File> getTestFiles() {
        List<File> testfiles = new ArrayList<>();
        testfiles.addAll(TestUtilities.findRelativeNestedJavaFiles("testing", "typecheck"));
        return testfiles;
    }
}
