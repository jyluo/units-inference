package backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import checkers.inference.solver.backend.encoder.AbstractConstraintEncoderFactory;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

/**
 * Abstract Z3 implementation of {@link
 * checkers.inference.solver.backend.encoder.ConstraintEncoderFactory} for integer theory.
 * Subclasses must specify the exact encoders used.
 *
 * @see checkers.inference.solver.backend.encoder.ConstraintEncoderFactory
 */
public abstract class GJEConstraintEncoderFactory<SlotEncodingT, SlotSolutionT>
        extends AbstractConstraintEncoderFactory<
                BoolExpr, GJEFormatTranslator<SlotEncodingT, SlotSolutionT>> {
    protected final Context ctx;

    public GJEConstraintEncoderFactory(
            Lattice lattice,
            Context ctx,
            GJEFormatTranslator<SlotEncodingT, SlotSolutionT> gjeFormatTranslator) {
        super(lattice, gjeFormatTranslator);
        this.ctx = ctx;
    }
}
