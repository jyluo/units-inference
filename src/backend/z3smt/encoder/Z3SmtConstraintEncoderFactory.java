package backend.z3smt.encoder;

import backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.solver.backend.encoder.AbstractConstraintEncoderFactory;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.Context;

/**
 * Abstract Z3 implementation of {@link
 * checkers.inference.solver.backend.encoder.ConstraintEncoderFactory} for integer theory.
 * Subclasses must specify the exact encoders used.
 *
 * @see checkers.inference.solver.backend.encoder.ConstraintEncoderFactory
 */
public abstract class Z3SmtConstraintEncoderFactory<
                SlotEncodingT, ConstraintEncodingT, SlotSolutionT>
        extends AbstractConstraintEncoderFactory<
                ConstraintEncodingT,
                Z3SmtFormatTranslator<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>> {
    protected final Context ctx;

    public Z3SmtConstraintEncoderFactory(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>
                    z3SmtFormatTranslator) {
        super(lattice, z3SmtFormatTranslator);
        this.ctx = ctx;
    }
}
