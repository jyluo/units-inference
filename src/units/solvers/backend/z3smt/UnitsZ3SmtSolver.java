package units.solvers.backend.z3smt;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.Z3SmtSolver;
import checkers.inference.InferenceMain;
import checkers.inference.model.ComparableConstraint;
import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.model.SubtypeConstraint;
import checkers.inference.model.serialization.ToStringSerializer;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.FileUtils;
import checkers.inference.solver.util.SolverEnvironment;
import com.microsoft.z3.Expr;
import java.io.File;
import java.util.Collection;
import org.checkerframework.javacutil.BugInCF;
import units.representation.TypecheckUnit;
import units.solvers.backend.z3smt.representation.Z3EquationSet;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsZ3SmtSolver extends Z3SmtSolver<Z3InferenceUnit, Z3EquationSet, TypecheckUnit> {

    public UnitsZ3SmtSolver(
            SolverEnvironment solverEnvironment,
            Collection<Slot> slots,
            Collection<Constraint> constraints,
            Z3SmtFormatTranslator<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
                    z3SmtFormatTranslator,
            Lattice lattice) {
        super(solverEnvironment, slots, constraints, z3SmtFormatTranslator, lattice);
    }

    @Override
    protected void encodeAllConstraints() {
        int current = 1;

        StringBuffer constraintSmtFileContents = new StringBuffer();

        for (Constraint constraint : constraints) {
            // System.err.println("Getting next item.");

            // System.err.println(
            // " Serializing Constraint " + current + " / " + total + " : " +
            // constraint);

            // if (current % 100 == 0) {
            // System.err.println("=== Running GC ===");
            // Runtime.getRuntime().gc(); // trigger garbage collector
            // }

            BoolExpr serializedConstraint = constraint.serialize(formatTranslator);

            // System.err.println(" Constraint serialized. ");

            if (serializedConstraint == null) {
                // TODO: Should error abort if unsupported constraint detected.
                // Currently warning is a workaround for making ontology
                // working, as in some cases existential constraints generated.
                // Should investigate on this, and change this to ErrorAbort
                // when eliminated unsupported constraints.
                System.err.println(
                        "Unsupported constraint detected! Constraint type: "
                                + constraint.getClass().getSimpleName());
                // current++;
                continue;
            }

            // System.err.println(" Constraint \n" + serializedConstraint
            // + "\n simplified :\n " + serializedConstraint.simplify());

            Expr simplifiedConstraint = serializedConstraint.simplify();

            if (simplifiedConstraint.isTrue()) {
                // This only works if the BoolExpr is directly the value Z3True.
                // Still a good
                // filter, but doesn't filter enough.
                // EG: (and (= false false) (= false false) (= 0 0) (= 0 0) (= 0
                // 0))
                // Skip tautology.
                // System.err.println(" simplified to tautology.");
                current++;
                continue;
            }

            if (simplifiedConstraint.isFalse()) {
                final ToStringSerializer toStringSerializer = new ToStringSerializer(false);
                throw new BugInCF(
                        "impossible constraint: "
                                + constraint.serialize(toStringSerializer)
                                + "\nSerialized:\n"
                                + serializedConstraint);
            }

            String clause = simplifiedConstraint.toString();

            if (!optimizingMode && getUnsatCore) {
                // add assertions with names, for unsat core dump
                String constraintName = constraint.getClass().getSimpleName() + current;

                constraintSmtFileContents.append("(assert (! ");
                constraintSmtFileContents.append(clause);
                constraintSmtFileContents.append(" :named " + constraintName + "))\n");

                // add constraint to serialized constraints map, so that we can
                // retrieve later using
                // the constraint name when outputting the unsat core
                serializedConstraints.put(constraintName, constraint);
            } else {
                constraintSmtFileContents.append("(assert ");
                constraintSmtFileContents.append(clause);
                constraintSmtFileContents.append(")\n");
            }

            // generate a soft constraint that we prefer equality for subtype
            // TODO: perhaps prefer not bottom and prefer not top will suffice?
            if (optimizingMode && constraint instanceof SubtypeConstraint) {
                SubtypeConstraint stc = (SubtypeConstraint) constraint;

                Constraint eqc =
                        InferenceMain.getInstance()
                                .getConstraintManager()
                                .createEqualityConstraint(stc.getSubtype(), stc.getSupertype());

                Expr simplifiedEQC = eqc.serialize(formatTranslator).simplify();

                if (!simplifiedEQC.isTrue()) {
                    constraintSmtFileContents.append("(assert-soft ");
                    constraintSmtFileContents.append(simplifiedEQC);
                    constraintSmtFileContents.append(" :weight 1)\n");
                }
            }

            // generate soft constraint for comparisons that their args are
            // equal
            if (optimizingMode && constraint instanceof ComparableConstraint) {
                ComparableConstraint cc = (ComparableConstraint) constraint;

                Constraint eqc =
                        InferenceMain.getInstance()
                                .getConstraintManager()
                                .createEqualityConstraint(cc.getFirst(), cc.getSecond());

                Expr simplifiedEQC = eqc.serialize(formatTranslator).simplify();

                if (!simplifiedEQC.isTrue()) {
                    constraintSmtFileContents.append("(assert-soft ");
                    constraintSmtFileContents.append(simplifiedEQC);
                    constraintSmtFileContents.append(" :weight 1)\n");
                }
            }

            current++;
            // System.err.println(" Added constraint. HasNext? " +
            // iter.hasNext());
        }

        String constraintSmt = constraintSmtFileContents.toString();

        smtFileContents.append(constraintSmt);

        // debug use
        // Write Constraints to file
        FileUtils.appendFile(new File(pathToProject + "/constraints.smt"), constraintSmt);
    }
}
