package units.util;

import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import com.microsoft.z3.BoolExpr;
import units.representation.TypecheckUnit;
import units.representation.UnitsRepresentationUtils;

/**
 * Utility class with methods for computing the result unit of various arithmetic operations.
 */
public class UnitsTypecheckUtils {

    public static TypecheckUnit multiplication(TypecheckUnit lhs, TypecheckUnit rhs) {
        TypecheckUnit result = new TypecheckUnit();

        // if either lhs or rhs is UnknownUnits or UnitsBottom, then result is UnknownUnits
        if (lhs.isUnknownUnits() || lhs.isUnitsBottom() || rhs.isUnknownUnits()
                || rhs.isUnitsBottom()) {
            result.setUnknownUnits(true);
            return result;
        }

        // otherwise res component = lhs component + rhs component
        result.setPrefixExponent(lhs.getPrefixExponent() + rhs.getPrefixExponent());
        for (String bu : UnitsRepresentationUtils.getInstance().baseUnits()) {
            result.setExponent(bu, lhs.getExponent(bu) + rhs.getExponent(bu));
        }

        return result;
    }

    public static AnnotationMirror multiplication(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        TypecheckUnit lhs = UnitsRepresentationUtils.getInstance().createTypecheckUnit(lhsAM);
        TypecheckUnit rhs = UnitsRepresentationUtils.getInstance().createTypecheckUnit(rhsAM);
        return UnitsRepresentationUtils.getInstance().createInternalUnit(multiplication(lhs, rhs));
    }

    public static TypecheckUnit division(TypecheckUnit lhs, TypecheckUnit rhs) {
        TypecheckUnit result = new TypecheckUnit();

        // if either lhs or rhs is UnknownUnits or UnitsBottom, then result is UnknownUnits
        if (lhs.isUnknownUnits() || lhs.isUnitsBottom() || rhs.isUnknownUnits()
                || rhs.isUnitsBottom()) {
            result.setUnknownUnits(true);
            return result;
        }

        // otherwise res component = lhs component - rhs component
        result.setPrefixExponent(lhs.getPrefixExponent() - rhs.getPrefixExponent());
        for (String bu : UnitsRepresentationUtils.getInstance().baseUnits()) {
            result.setExponent(bu, lhs.getExponent(bu) - rhs.getExponent(bu));
        }

        return result;
    }

    public static AnnotationMirror division(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        TypecheckUnit lhs = UnitsRepresentationUtils.getInstance().createTypecheckUnit(lhsAM);
        TypecheckUnit rhs = UnitsRepresentationUtils.getInstance().createTypecheckUnit(rhsAM);
        return UnitsRepresentationUtils.getInstance().createInternalUnit(division(lhs, rhs));
    }

    public static boolean unitsEqual(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        TypecheckUnit lhs = UnitsRepresentationUtils.getInstance().createTypecheckUnit(lhsAM);
        TypecheckUnit rhs = UnitsRepresentationUtils.getInstance().createTypecheckUnit(rhsAM);
        return lhs.equals(rhs);
    }

    public static boolean unitsSubtype(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();
        if (AnnotationUtils.areSame(lhsAM, unitsRepUtils.BOTTOM)
                || AnnotationUtils.areSame(rhsAM, unitsRepUtils.TOP)) {
            return true;
        } else {
            return unitsEqual(lhsAM, rhsAM);
        }
    }
}
