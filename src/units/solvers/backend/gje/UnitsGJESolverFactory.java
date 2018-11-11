package units.solvers.backend.gje;

import backend.gje.GJEFormatTranslator;
import backend.gje.GJESolverFactory;
import checkers.inference.solver.frontend.Lattice;
import units.representation.TypecheckUnit;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsGJESolverFactory extends GJESolverFactory<Z3InferenceUnit, TypecheckUnit> {

    @Override
    protected GJEFormatTranslator<Z3InferenceUnit, TypecheckUnit> createFormatTranslator(
            Lattice lattice) {
        return new UnitsGJEFormatTranslator(lattice);
    }
}
