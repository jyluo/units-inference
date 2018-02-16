package units.solvers.backend.z3smt;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.Z3SmtSolverFactory;
import checkers.inference.solver.frontend.Lattice;
import units.internalrepresentation.InferenceUnit;
import units.internalrepresentation.TypecheckUnit;

public class UnitsZ3SmtSolverFactory extends Z3SmtSolverFactory<InferenceUnit, TypecheckUnit> {

    @Override
    protected Z3SmtFormatTranslator<InferenceUnit, TypecheckUnit> createFormatTranslator(
            Lattice lattice) {
        return new UnitsZ3SmtFormatTranslator(lattice);
    }
}
