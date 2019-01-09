package units.solvers.backend.z3smt;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.Z3SmtSolverFactory;
import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.SolverEnvironment;
import java.util.Collection;
import units.representation.TypecheckUnit;
import units.solvers.backend.z3smt.representation.Z3EquationSet;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsZ3SmtSolverFactory
        extends Z3SmtSolverFactory<Z3InferenceUnit, Z3EquationSet, TypecheckUnit> {

    @Override
    protected Z3SmtFormatTranslator<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
            createFormatTranslator(Lattice lattice) {
        return new UnitsZ3SmtFormatTranslator(lattice);
    }

    @Override
    public Solver<?> createSolver(
            SolverEnvironment solverOptions,
            Collection<Slot> slots,
            Collection<Constraint> constraints,
            Lattice lattice) {
        return new UnitsZ3SmtSolver(
                solverOptions, slots, constraints, createFormatTranslator(lattice), lattice);
    }
}
