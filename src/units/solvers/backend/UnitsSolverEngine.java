package units.solvers.backend;

import checkers.inference.solver.SolverEngine;
import checkers.inference.solver.backend.SolverFactory;
import units.solvers.backend.z3smt.UnitsZ3SmtSolverFactory;

public class UnitsSolverEngine extends SolverEngine {
    @Override
    protected SolverFactory createSolverFactory() {
        return new UnitsZ3SmtSolverFactory();
    }
}
