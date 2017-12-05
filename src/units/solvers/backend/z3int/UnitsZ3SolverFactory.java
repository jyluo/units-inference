package units.solvers.backend.z3int;

import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.Z3IntSolverFactory;
import checkers.inference.solver.frontend.Lattice;

public class UnitsZ3SolverFactory extends Z3IntSolverFactory {
    @Override
    protected Z3IntFormatTranslator createFormatTranslator(Lattice lattice) {
        return new UnitsZ3FormatTranslator(lattice);
    }
}
