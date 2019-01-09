package backend.z3smt;

import checkers.inference.solver.backend.AbstractSolverFactory;

public abstract class Z3SmtSolverFactory<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>
        extends AbstractSolverFactory<
                Z3SmtFormatTranslator<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>> {}
