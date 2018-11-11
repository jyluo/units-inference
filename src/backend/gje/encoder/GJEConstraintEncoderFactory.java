package backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import checkers.inference.solver.backend.encoder.AbstractConstraintEncoderFactory;
import checkers.inference.solver.frontend.Lattice;
import units.solvers.backend.gje.representation.GJEEquationSet;

/**
 * Abstract Z3 implementation of {@link
 * checkers.inference.solver.backend.encoder.ConstraintEncoderFactory} for integer theory.
 * Subclasses must specify the exact encoders used.
 *
 * @see checkers.inference.solver.backend.encoder.ConstraintEncoderFactory
 */
public abstract class GJEConstraintEncoderFactory<SlotEncodingT, SlotSolutionT>
        extends AbstractConstraintEncoderFactory<
                GJEEquationSet, GJEFormatTranslator<SlotEncodingT, SlotSolutionT>> {
    public GJEConstraintEncoderFactory(
            Lattice lattice,
            GJEFormatTranslator<SlotEncodingT, SlotSolutionT> gjeFormatTranslator) {
        super(lattice, gjeFormatTranslator);
    }
}