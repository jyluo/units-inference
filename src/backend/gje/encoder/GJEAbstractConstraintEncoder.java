package backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import checkers.inference.solver.backend.encoder.AbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.solvers.backend.gje.representation.GJEEquationSet;

/** Abstract base class for every Z3Int constraint encoders. */
public class GJEAbstractConstraintEncoder<SlotEncodingT, SlotSolutionT>
        extends AbstractConstraintEncoder<GJEEquationSet> {

    protected final GJEFormatTranslator<SlotEncodingT, SlotSolutionT> gjeFormatTranslator;

    public GJEAbstractConstraintEncoder(
            Lattice lattice,
            GJEFormatTranslator<SlotEncodingT, SlotSolutionT> gjeFormatTranslator) {
        // empty value is an empty equation set, contradictory value is a contradictory set
        super(lattice, new GJEEquationSet(), new GJEEquationSet(true));
        this.gjeFormatTranslator = gjeFormatTranslator;
    }
}
