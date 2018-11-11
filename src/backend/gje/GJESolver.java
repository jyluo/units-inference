package backend.gje;

import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.model.serialization.ToStringSerializer;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.PrintUtils.UniqueSlotCollector;
import checkers.inference.solver.util.SolverEnvironment;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Logger;
import javax.lang.model.element.AnnotationMirror;

// GaussJordanElimination solver
public class GJESolver<SlotEncodingT, SlotSolutionT>
        extends Solver<GJEFormatTranslator<SlotEncodingT, SlotSolutionT>> {

    protected final Logger logger = Logger.getLogger(GJESolver.class.getName());

    protected StringBuffer smtFileContents;

    // maps serialized slot ID to the slot objects
    protected final Map<Long, Slot> slotGJEtoCFIMap = new HashMap<>();
    protected final Map<Slot, Long> slotCFItoGJEMap = new HashMap<>();

    // file is written at projectRootFolder/constraints.smt
    protected static final String pathToProject =
            new File(new File("").getAbsolutePath()).toString();
    protected static final String constraintsFilePrefix = pathToProject + "/gjeConstraints";
    protected static final String constraintsFileExtension = ".gje";

    // timing statistics variables
    protected long serializationStart;
    protected long serializationEnd;
    protected long solvingStart;
    protected long solvingEnd;

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

        encodeAllSlots();

        encodeAllConstraints();

        solvingStart = System.currentTimeMillis();
        // in Units, if the status is SAT then there must be output in the model
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

    private List<String> runSolver() {
        return null;
    }

    @Override
    public Collection<Constraint> explainUnsatisfiable() {

        List<Constraint> unsatConstraints = new ArrayList<>();

        return unsatConstraints;
    }

    protected void encodeAllSlots() {
        long count = 1;

        final ToStringSerializer toStringSerializer = new ToStringSerializer(false);

        System.out.println("== Slot serialization map ==");
        // get a set of unique slots used in the constraints
        UniqueSlotCollector slotsCollector = new UniqueSlotCollector();
        for (Constraint constraint : constraints) {
            constraint.serialize(slotsCollector);
        }

        for (VariableSlot slot : slotsCollector.getSlots()) {
            slotGJEtoCFIMap.put(count, slot);
            slotCFItoGJEMap.put(slot, count);
            count++;
            System.out.println("ID: " + count + " --> slot " + slot.serialize(toStringSerializer));
        }
    }

    @Override
    protected void encodeAllConstraints() {
        int current = 1;

        StringBuffer constraintSmtFileContents = new StringBuffer();

        for (Constraint constraint : constraints) {

            BoolExpr serializedConstraint = constraint.serialize(formatTranslator);

            if (serializedConstraint == null) {
                System.out.println(
                        "Unsupported constraint detected! Constraint type: "
                                + constraint.getClass().getSimpleName());
                continue;
            }

            Expr simplifiedConstraint = serializedConstraint.simplify();

            if (simplifiedConstraint.isTrue()) {
                current++;
                continue;
            }
        }
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
}
