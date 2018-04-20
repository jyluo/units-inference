package backend.z3smt;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import javax.lang.model.element.AnnotationMirror;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Statistics;
import checkers.inference.InferenceMain;
import checkers.inference.model.ComparableConstraint;
import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.model.SubtypeConstraint;
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

        // creating solver with timeout
        // Map<String, String> z3Args = new HashMap<>();
        // int timeout = 2 * 60 * 1000; // timeout of 2 mins
        // z3Args.put("timeout", Integer.toString(timeout));
        // ctx = new Context(z3Args);

        // creating solver without timeout
        ctx = new Context();

        solver = ctx.mkOptimize();
        z3SmtFormatTranslator.init(ctx, solver);
    }

    // Main entry point
    @Override
    public Map<Integer, AnnotationMirror> solve() {
        Map<Integer, AnnotationMirror> result;

        Runtime.getRuntime().gc(); // trigger garbage collector

        System.out.println("Now encoding slots with soft constraints");

        encodeAllSlots();

        Runtime.getRuntime().gc(); // trigger garbage collector

        encodeAllConstraints();

        System.out.println("Encoding constraints done!");

        Runtime.getRuntime().gc(); // trigger garbage collector

        System.out.println("=== Solver statistics ===");
        Statistics stats = solver.getStatistics();
        for (String key : stats.getKeys()) {
            System.out.println("  " + key + " => " + stats.get(key));
        }

        System.out.println("Starting the solving");
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
                solver.Assert(formatTranslator.encodeSlotWellformnessConstraint(varSlot));
                solver.AssertSoft(formatTranslator.encodeSlotPreferenceConstraint(varSlot), 1,
                        "g1");
            }
        }
    }

    @Override
    protected void encodeAllConstraints() {
        int total = constraints.size();

        int current = 1;

        Iterator<Constraint> iter = constraints.iterator();

        while (iter.hasNext()) {
            // System.out.println("Getting next item.");

            Constraint constraint = iter.next();

            System.out.println(
                    "  Serializing Constraint " + current + " / " + total + " : " + constraint);

            if (current % 100 == 0) {
                System.out.println("=== Running GC ===");
                Runtime.getRuntime().gc(); // trigger garbage collector
            }

            // generate soft constraint for comparisons that their args are equal
            if (constraint instanceof ComparableConstraint) {
                ComparableConstraint compC = (ComparableConstraint) constraint;

                Constraint eqC = InferenceMain.getInstance().getConstraintManager()
                        .createEqualityConstraint(compC.getFirst(), compC.getSecond());

                BoolExpr serializedEqC = eqC.serialize(formatTranslator);

                if (!serializedEqC.simplify().isTrue()) {
                    solver.AssertSoft(serializedEqC, 1, "g1");
                }
            }

            // generate soft constraint for subtype that they are equal
            if (constraint instanceof SubtypeConstraint) {
                SubtypeConstraint stC = (SubtypeConstraint) constraint;

                Constraint eqC = InferenceMain.getInstance().getConstraintManager()
                        .createEqualityConstraint(stC.getSubtype(), stC.getSupertype());

                BoolExpr serializedEqC = eqC.serialize(formatTranslator);

                if (!serializedEqC.simplify().isTrue()) {
                    solver.AssertSoft(serializedEqC, 1, "g1");
                }
            }

            BoolExpr serializedConstraint = constraint.serialize(formatTranslator);

            // System.out.println(" Constraint serialized. ");

            if (serializedConstraint == null) {
                // TODO: Should error abort if unsupported constraint detected.
                // Currently warning is a workaround for making ontology working, as in some cases
                // existential constraints generated.
                // Should investigate on this, and change this to ErrorAbort when eliminated
                // unsupported constraints.
                InferenceMain.getInstance().logger
                        .warning("Unsupported constraint detected! Constraint type: "
                                + constraint.getClass());
                current++;
                continue;
            }

            // System.out.println(" Constraint \n" + serializedConstraint
            // + "\n simplified :\n " + serializedConstraint.simplify());

            if (serializedConstraint.simplify().isTrue()) {
                // This only works if the BoolExpr is directly the value Z3True. Still a good
                // filter, but doesn't filter enough.
                // EG: (and (= false false) (= false false) (= 0 0) (= 0 0) (= 0 0))
                // Skip tautology.
                // System.out.println(" simplified to tautology.");
                current++;
                continue;
            }

            // System.out.println(" Adding hard constraint ");

            solver.Assert(serializedConstraint);

            current++;
            // System.out.println(" Added constraint. HasNext? " + iter.hasNext());
        }
    }

    @Override
    public Collection<Constraint> explainUnsatisfiable() {
        // TODO in the future
        return null;
    }
}
