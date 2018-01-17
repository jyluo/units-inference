package units.solvers.backend;

import checkers.inference.solver.SolverEngine;
import checkers.inference.solver.backend.SolverFactory;
import units.solvers.backend.z3int.UnitsZ3SolverFactory;

public class UnitsSolverEngine extends SolverEngine {
//    @SuppressWarnings("unchecked")
    @Override
    protected SolverFactory createSolverFactory() {
        return new UnitsZ3SolverFactory();
//        // --solverArgs="collectStatistic=true,solver=Z3Int"
//        if (NameUtils.getSolverName((Class<? extends Solver<?>>) Z3IntSolver.class)
//                .equals(solverName)) {
//            return new UnitsZ3SolverFactory();
//        } else {
//            return super.createSolverFactory();
//        }
    }
}
