package backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import checkers.inference.solver.backend.encoder.AbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;

/** Abstract base class for every Z3Int constraint encoders. */
public class GJEAbstractConstraintEncoder<SlotEncodingT, SlotSolutionT>
        extends AbstractConstraintEncoder<String> {

    protected final GJEFormatTranslator<SlotEncodingT, SlotSolutionT> gjeFormatTranslator;

    public GJEAbstractConstraintEncoder(
            Lattice lattice,
            GJEFormatTranslator<SlotEncodingT, SlotSolutionT> gjeFormatTranslator) {
        // empty value is z3True, contradictory value is z3False
        super(lattice, "True", "False");
        this.gjeFormatTranslator = gjeFormatTranslator;
    }
}
