package units.solvers.backend.z3int;

import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.Z3IntSolverFactory;
import checkers.inference.solver.frontend.Lattice;
import units.internalrepresentation.InferenceUnit;
import units.internalrepresentation.TypecheckUnit;

public class UnitsZ3SolverFactory extends Z3IntSolverFactory<InferenceUnit, TypecheckUnit> {

    @Override
    protected Z3IntFormatTranslator<InferenceUnit, TypecheckUnit> createFormatTranslator(
            Lattice lattice) {
        return new UnitsZ3FormatTranslator(lattice);
    }
}
