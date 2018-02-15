package checkers.inference.solver.backend.z3smt.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.solver.backend.encoder.AbstractConstraintEncoderFactory;
import checkers.inference.solver.backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.solver.frontend.Lattice;

/**
 * Abstract Z3 implementation of
 * {@link checkers.inference.solver.backend.encoder.ConstraintEncoderFactory} for integer theory.
 * Subclasses must specify the exact encoders used.
 *
 * @see checkers.inference.solver.backend.encoder.ConstraintEncoderFactory
 */
public abstract class Z3SmtConstraintEncoderFactory<SlotEncodingT, SlotSolutionT>
        extends AbstractConstraintEncoderFactory<BoolExpr> {
    protected final Context ctx;
    protected final Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT> z3IntFormatTranslator;

    public Z3SmtConstraintEncoderFactory(Lattice lattice, Context ctx,
            Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT> z3IntFormatTranslator) {
        super(lattice);
        this.ctx = ctx;
        this.z3IntFormatTranslator = z3IntFormatTranslator;
    }
}
