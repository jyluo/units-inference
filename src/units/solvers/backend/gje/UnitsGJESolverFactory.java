package units.solvers.backend.gje;

import backend.gje.GJEFormatTranslator;
import backend.gje.GJESolverFactory;
import checkers.inference.solver.frontend.Lattice;
import units.representation.TypecheckUnit;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

public class UnitsGJESolverFactory extends GJESolverFactory<GJEInferenceUnit, TypecheckUnit> {

    @Override
    protected GJEFormatTranslator<GJEInferenceUnit, TypecheckUnit> createFormatTranslator(
            Lattice lattice) {
        return new UnitsGJEFormatTranslator(lattice);
    }
}
