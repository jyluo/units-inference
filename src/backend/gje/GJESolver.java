package backend.gje;

import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.model.serialization.ToStringSerializer;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.FileUtils;
import checkers.inference.solver.util.SolverEnvironment;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;
import java.util.logging.Logger;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.javacutil.BugInCF;
import units.solvers.backend.gje.representation.GJEEquationSet;

// GaussJordanElimination solver
public class GJESolver<SlotEncodingT, SlotSolutionT>
        extends Solver<GJEFormatTranslator<SlotEncodingT, SlotSolutionT>> {

    protected final Logger logger = Logger.getLogger(GJESolver.class.getName());

    // file is written at projectRootFolder/gjeConstraints_<dimension>.gje
    protected static final Path pathToProject = Paths.get(System.getProperty("user.dir"));
    protected static final Path constraintsFilePrefix =
            Paths.get(pathToProject.toString(), "gjeConstraints");
    protected static final String constraintsFileExtension = ".gje";

    // timing statistics variables
    protected long serializationStart;
    protected long serializationEnd;
    protected long solvingStart;
    protected long solvingEnd;

    // number of GJE variables
    protected int numOfGJEVariables;

    public GJESolver(
            SolverEnvironment solverEnvironment,
            Collection<Slot> slots,
            Collection<Constraint> constraints,
            GJEFormatTranslator<SlotEncodingT, SlotSolutionT> z3SmtFormatTranslator,
            Lattice lattice) {
        super(solverEnvironment, slots, constraints, z3SmtFormatTranslator, lattice);
    }

    // Main entry point
    @Override
    public Map<Integer, AnnotationMirror> solve() {
        Map<Integer, AnnotationMirror> result;

        serializationStart = System.currentTimeMillis();
        numOfGJEVariables = formatTranslator.assignGJEVarIDs(constraints);
        encodeAllConstraints();
        serializationEnd = System.currentTimeMillis();

        solvingStart = System.currentTimeMillis();
        List<String> results = runSolver();
        solvingEnd = System.currentTimeMillis();

        if (results != null) {
            result =
                    formatTranslator.decodeSolution(
                            results, solverEnvironment.processingEnvironment);
        } else {
            System.out.println("\n\n!!! The set of constraints is unsatisfiable! !!!");
            result = null;
        }

        return result;
    }

    @Override
    protected void encodeAllConstraints() {

        final ToStringSerializer toStringSerializer = new ToStringSerializer(false);

        GJEEquationSet totalEquationSet = new GJEEquationSet();

        for (Constraint constraint : constraints) {

            System.out.println("Serializing " + constraint.serialize(toStringSerializer));

            GJEEquationSet serializedConstraint = constraint.serialize(formatTranslator);

            if (serializedConstraint == null) {
                System.out.println(
                        "Unsupported constraint detected! Constraint type: "
                                + constraint.getClass().getSimpleName());
                continue;
            } else if (serializedConstraint.isContradiction()) {
                // TODO: proper error reporter abort
                throw new BugInCF(
                        "the constraint "
                                + constraint.serialize(toStringSerializer)
                                + " is contradictory");
            } else if (!serializedConstraint.isEmpty()) {
                totalEquationSet.union(serializedConstraint);
            }

            System.out.println(serializedConstraint.toString());
        }

        System.out.println("Total equation set:");
        System.out.println(totalEquationSet);

        // serialize into files
        writeGJEFiles(totalEquationSet.getEquationSet());
    }

    private void writeGJEFiles(Map<String, Set<String>> eqSet) {
        for (Entry<String, Set<String>> entry : eqSet.entrySet()) {
            String dimension = entry.getKey();
            Set<String> equations = entry.getValue();

            String fileName =
                    constraintsFilePrefix.toString() + "_" + dimension + constraintsFileExtension;

            File outFile = new File(fileName);

            FileUtils.writeFile(outFile, generateGJEFileContent(equations));

            System.out.println(
                    "GJE eqs for "
                            + dimension
                            + " have been written to: "
                            + outFile.getAbsolutePath()
                            + System.lineSeparator());
        }
    }

    private String generateGJEFileContent(Set<String> equations) {
        StringBuffer sb = new StringBuffer();
        // # of variables
        sb.append(numOfGJEVariables);
        sb.append(System.lineSeparator());
        // # of rows
        sb.append(equations.size());
        sb.append(System.lineSeparator());
        // sort and write each equation out
        for (String eq : new TreeSet<>(equations)) {
            sb.append(eq);
            sb.append(System.lineSeparator());
        }
        return sb.toString();
    }

    private List<String> runSolver() {
        // TODO
        return null;
    }

    // outputs
    private void parseStdOut(BufferedReader stdOut, List<String> results) {
        String line = "";

        try {
            while ((line = stdOut.readLine()) != null) {}

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public Collection<Constraint> explainUnsatisfiable() {
        // TODO
        List<Constraint> unsatConstraints = new ArrayList<>();
        return unsatConstraints;
    }
}
