package units.solvers.backend;

import checkers.inference.solver.SolverEngine;
import checkers.inference.solver.backend.SolverFactory;
import checkers.inference.solver.util.PrintUtils;
import units.solvers.backend.z3smt.UnitsZ3SmtSolverFactory;

public class UnitsSolverEngine extends SolverEngine {
    @Override
    protected SolverFactory createSolverFactory() {
        return new UnitsZ3SmtSolverFactory();
    }

    // TODO: would be nice to be able to override recordSlotConstraintSize() in
    // super to track # of custom slots and constraints
}
