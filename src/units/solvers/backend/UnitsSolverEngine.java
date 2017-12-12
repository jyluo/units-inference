package units.solvers.backend;

import checkers.inference.solver.SolverEngine;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.backend.SolverFactory;
import checkers.inference.solver.backend.z3Int.Z3IntSolver;
import checkers.inference.solver.util.NameUtils;
import units.solvers.backend.z3int.UnitsZ3SolverFactory;

public class UnitsSolverEngine extends SolverEngine {
    @SuppressWarnings("unchecked")
    @Override
    protected SolverFactory createSolverFactory() {
        // --solverArgs="collectStatistic=true,solver=Z3Int"
        if (NameUtils.getSolverName((Class<? extends Solver<?>>) Z3IntSolver.class)
                .equals(solverName)) {
            return new UnitsZ3SolverFactory();
        } else {
            return super.createSolverFactory();
        }
    }
}
