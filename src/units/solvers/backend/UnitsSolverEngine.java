package units.solvers.backend;

import checkers.inference.solver.SolverEngine;
import checkers.inference.solver.backend.SolverFactory;
import org.checkerframework.javacutil.BugInCF;
import units.solvers.backend.gje.UnitsGJESolverFactory;
import units.solvers.backend.z3smt.UnitsZ3SmtSolverFactory;

public class UnitsSolverEngine extends SolverEngine {
    @Override
    protected SolverFactory createSolverFactory() {
        if (solverName.contentEquals("Z3smt")) {
            return new UnitsZ3SmtSolverFactory();
        } else if (solverName.contentEquals("GJE")) {
            return new UnitsGJESolverFactory();
        } else {
            throw new BugInCF(
                    "A back end solver (Z3smt, GJE) must be supplied in solverArgs: solver=Z3smt");
        }
    }
}
