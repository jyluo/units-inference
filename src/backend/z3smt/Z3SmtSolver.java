package backend.z3smt;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import javax.lang.model.element.AnnotationMirror;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.InferenceMain;
import checkers.inference.model.Constraint;
import checkers.inference.model.EqualityConstraint;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.SolverEnvironment;

public class Z3SmtSolver<SlotEncodingT, SlotSolutionT>
        extends Solver<Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT>> {

    protected final Context ctx;
    protected final com.microsoft.z3.Optimize solver;

    public Z3SmtSolver(SolverEnvironment solverEnvironment, Collection<Slot> slots,
            Collection<Constraint> constraints,
            Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT> z3SmtFormatTranslator,
            Lattice lattice) {
        super(solverEnvironment, slots, constraints, z3SmtFormatTranslator, lattice);
        ctx = new Context();
        solver = ctx.mkOptimize();
        z3SmtFormatTranslator.init(ctx, solver);
    }

    // Main entry point
    @Override
    public Map<Integer, AnnotationMirror> solve() {
        Map<Integer, AnnotationMirror> result;

        encodeAllSlots();
        encodeAllConstraints();

        switch (solver.Check()) {
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

    protected void encodeAllSlots() {
        for (Slot slot : slots) {
            if (slot instanceof VariableSlot) {
                VariableSlot varSlot = (VariableSlot) slot;
                solver.Add(formatTranslator.encodeSlotWellformnessConstraint(varSlot));
                solver.AssertSoft(formatTranslator.encodeSlotPreferenceConstraint(varSlot), 1,
                        "default-constraint-group");
            }
        }
    }

    protected String getSoftConstraintGroup() {
        return Double.toString(Math.random());
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

//            // Hack: encode soft equality constraints as soft constraints
//            // TODO: move to more precise locations
//            if (constraint instanceof EqualityConstraint) {
//                EqualityConstraint etc = (EqualityConstraint) constraint;
//
//                if (etc.isSoftConstraint()) {
//                    // System.out.println( " === inserting soft EQ constraint " + constraint);
//                    solver.AssertSoft(serializedConstraint, 1, getSoftConstraintGroup());
//                    continue;
//                }
//            }

            solver.Add(serializedConstraint);
        }
    }

    @Override
    public Collection<Constraint> explainUnsatisfiable() {
        // TODO in the future
        return null;
    }
}
