package units.solvers.backend.gje;

import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.solver.backend.AbstractSolverFactory;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.SolverEnvironment;
import java.util.Collection;

public class UnitsGJESolverFactory extends AbstractSolverFactory<UnitsGJEFormatTranslator> {

    @Override
    public Solver<?> createSolver(
            SolverEnvironment solverEnvironment,
            Collection<Slot> slots,
            Collection<Constraint> constraints,
            Lattice lattice) {
        UnitsGJEFormatTranslator formatTranslator = createFormatTranslator(lattice);
        return new UnitsGJESolver(solverEnvironment, slots, constraints, formatTranslator, lattice);
    }

    @Override
    protected UnitsGJEFormatTranslator createFormatTranslator(Lattice lattice) {
        return new UnitsGJEFormatTranslator(lattice);
    }
}
