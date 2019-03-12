package units.solvers.backend.gje;

import checkers.inference.InferenceMain;
import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.solver.backend.AbstractSolverFactory;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.SolverEnvironment;
import java.util.Collection;
import units.UnitsInferenceAnnotatedTypeFactory;

public class UnitsGJESolverFactory extends AbstractSolverFactory<UnitsGJEFormatTranslator> {

    @Override
    public Solver<?> createSolver(
            SolverEnvironment solverEnvironment,
            Collection<Slot> slots,
            Collection<Constraint> constraints,
            Lattice lattice) {
        return new UnitsGJESolver(
                solverEnvironment, slots, constraints, createFormatTranslator(lattice), lattice);
    }

    @Override
    protected UnitsGJEFormatTranslator createFormatTranslator(Lattice lattice) {
        UnitsInferenceAnnotatedTypeFactory unitsIATF =
                (UnitsInferenceAnnotatedTypeFactory)
                        InferenceMain.getInstance().getRealTypeFactory();
        return new UnitsGJEFormatTranslator(
                lattice,
                unitsIATF.getUnitsRepresentationUtils(),
                unitsIATF.getUnitsTypecheckUtils());
    }
}
