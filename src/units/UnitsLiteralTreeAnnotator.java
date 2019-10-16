package units;

import org.checkerframework.framework.qual.LiteralKind;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import units.representation.UnitsRepresentationUtils;

/** Common base class for LiteralTreeAnnotator. */
public abstract class UnitsLiteralTreeAnnotator extends LiteralTreeAnnotator {

    UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();

    // Programmatically set the qualifier for literals
    public UnitsLiteralTreeAnnotator(AnnotatedTypeFactory atf) {
        super(atf);

        // set BOTTOM as the literal qualifier for null literals
        addLiteralKind(LiteralKind.NULL, unitsRepUtils.BOTTOM);
        addLiteralKind(LiteralKind.STRING, unitsRepUtils.DIMENSIONLESS);
        addLiteralKind(LiteralKind.CHAR, unitsRepUtils.DIMENSIONLESS);
        addLiteralKind(LiteralKind.BOOLEAN, unitsRepUtils.DIMENSIONLESS);

        // TODO: set BOTTOM as the literal qualifier for lower bounds? Its nice to
        // infer a bound which is the current mode.
    }
}
