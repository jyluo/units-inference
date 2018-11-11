package units.solvers.backend.gje;

import backend.gje.GJEFormatTranslator;
import backend.gje.GJESolverFactory;
import checkers.inference.solver.frontend.Lattice;
import units.representation.InferenceUnit;
import units.representation.TypecheckUnit;

public class UnitsGJESolverFactory extends GJESolverFactory<InferenceUnit, TypecheckUnit> {

    @Override
    protected GJEFormatTranslator<InferenceUnit, TypecheckUnit> createFormatTranslator(
            Lattice lattice) {
        return new UnitsGJEFormatTranslator(lattice);
    }
}
