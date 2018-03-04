package backend.z3smt;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import javax.lang.model.element.AnnotationMirror;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.InferenceMain;
import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.SolverEnvironment;

public class Z3SmtSolver<SlotEncodingT, SlotSolutionT>
        extends Solver<Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT>> {

    protected final Context ctx;
    protected final com.microsoft.z3.Solver solver;

    public Z3SmtSolver(SolverEnvironment solverEnvironment, Collection<Slot> slots,
            Collection<Constraint> constraints,
            Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT> z3SmtFormatTranslator,
            Lattice lattice) {
        super(solverEnvironment, slots, constraints, z3SmtFormatTranslator, lattice);
        ctx = new Context();
        solver = ctx.mkSolver();
        z3SmtFormatTranslator.initContext(ctx);
        z3SmtFormatTranslator.initSolver(solver);
    }

    // Main entry point
    @Override
    public Map<Integer, AnnotationMirror> solve() {
        Map<Integer, AnnotationMirror> result;

        encodeAllConstraints();

        switch (solver.check()) {
            case SATISFIABLE:
                result = formatTranslator.decodeSolution(solver.getModel(),
                        solverEnvironment.processingEnvironment);
                break;
            case UNSATISFIABLE:
                System.out.println("\n\n!!! The set of constraints is unsatisfiable! !!!");
                result = new HashMap<>();
                break;
            case UNKNOWN:
            default:
                System.out.println("\n\n!!! Solver failed to solve due to Unknown reason! !!!");
                result = new HashMap<>();
                break;
        }
        return result;
    }

    @Override
    protected void encodeAllConstraints() {
        for (Constraint constraint : constraints) {
            BoolExpr serializedConstraint = constraint.serialize(formatTranslator);

            if (serializedConstraint == null) {
                // TODO: Should error abort if unsupported constraint detected.
                // Currently warning is a workaround for making ontology working, as in some cases
                // existential constraints generated.
                // Should investigate on this, and change this to ErrorAbort when eliminated
                // unsupported constraints.
                InferenceMain.getInstance().logger
                        .warning("Unsupported constraint detected! Constraint type: "
                                + constraint.getClass());
                continue;
            }

            if (serializedConstraint.simplify().isTrue()) {
                // This only works if the BoolExpr is directly the value Z3True. Still a good
                // filter, but doesn't filter enough.
                // EG: (and (= false false) (= false false) (= 0 0) (= 0 0) (= 0 0))
                // Skip tautology.
                continue;
            }

            solver.add(serializedConstraint);
        }
    }

    @Override
    public Collection<Constraint> explainUnsatisfiable() {
        // TODO in the future
        return null;
    }
}
