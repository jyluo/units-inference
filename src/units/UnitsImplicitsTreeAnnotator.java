package units;

import org.checkerframework.framework.qual.LiteralKind;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import units.representation.UnitsRepresentationUtils;

/** Common base class for ImplicitsTreeAnnotator. */
public abstract class UnitsImplicitsTreeAnnotator extends ImplicitsTreeAnnotator {

    UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();

    // Programmatically set the qualifier implicits
    public UnitsImplicitsTreeAnnotator(AnnotatedTypeFactory atf) {
        super(atf);

        // set BOTTOM as the implicit qualifier for null literals
        addLiteralKind(LiteralKind.NULL, unitsRepUtils.BOTTOM);
        addLiteralKind(LiteralKind.STRING, unitsRepUtils.DIMENSIONLESS);
        addLiteralKind(LiteralKind.CHAR, unitsRepUtils.DIMENSIONLESS);
        addLiteralKind(LiteralKind.BOOLEAN, unitsRepUtils.DIMENSIONLESS);

        // TODO: set BOTTOM as the implicit qualifier for lower bounds? Its nice to
        // infer a bound which is the current mode.
    }
}
