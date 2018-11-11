package backend.gje;

import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.solver.backend.AbstractSolverFactory;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.SolverEnvironment;
import java.util.Collection;

public abstract class GJESolverFactory<SlotEncodingT, SlotSolutionT>
        extends AbstractSolverFactory<GJEFormatTranslator<SlotEncodingT, SlotSolutionT>> {

    @Override
    public Solver<?> createSolver(
            SolverEnvironment solverEnvironment,
            Collection<Slot> slots,
            Collection<Constraint> constraints,
            Lattice lattice) {
        GJEFormatTranslator<SlotEncodingT, SlotSolutionT> formatTranslator =
                createFormatTranslator(lattice);
        return new GJESolver<SlotEncodingT, SlotSolutionT>(
                solverEnvironment, slots, constraints, formatTranslator, lattice);
    }
}
