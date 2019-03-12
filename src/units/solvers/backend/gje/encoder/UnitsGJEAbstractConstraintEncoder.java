package units.solvers.backend.gje.encoder;

import checkers.inference.solver.backend.encoder.AbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.solvers.backend.gje.UnitsGJEFormatTranslator;
import units.solvers.backend.gje.representation.GJEEquationSet;
import units.utils.UnitsRepresentationUtils;

/** Abstract base class for every Z3Int constraint encoders. */
public class UnitsGJEAbstractConstraintEncoder extends AbstractConstraintEncoder<GJEEquationSet> {

    protected final UnitsGJEFormatTranslator formatTranslator;

    protected final UnitsRepresentationUtils unitsRepUtils;

    protected final UnitsGJEEncoderUtils unitsGJEEncoderUtils;

    public UnitsGJEAbstractConstraintEncoder(
            Lattice lattice, UnitsGJEFormatTranslator formatTranslator) {
        // empty value is an empty equation set, contradictory value is a contradictory set
        super(lattice, new GJEEquationSet(), new GJEEquationSet(true));
        this.formatTranslator = formatTranslator;
        this.unitsRepUtils = formatTranslator.getUnitsRepresentationUtils();
        this.unitsGJEEncoderUtils = formatTranslator.getUnitsGJEEncoderUtils();
    }
}
