package units.util;

import javax.lang.model.element.AnnotationMirror;
import units.internalrepresentation.TypecheckUnit;

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
        for (String bu : UnitsUtils.baseUnits()) {
            result.setExponent(bu, lhs.getExponent(bu) + rhs.getExponent(bu));
        }

        return result;
    }

    public static AnnotationMirror multiplication(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        TypecheckUnit lhs = UnitsUtils.createTypecheckUnit(lhsAM);
        TypecheckUnit rhs = UnitsUtils.createTypecheckUnit(rhsAM);
        return UnitsUtils.createInternalUnit(multiplication(lhs, rhs));
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
        for (String bu : UnitsUtils.baseUnits()) {
            result.setExponent(bu, lhs.getExponent(bu) - rhs.getExponent(bu));
        }

        return result;
    }

    public static AnnotationMirror division(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        TypecheckUnit lhs = UnitsUtils.createTypecheckUnit(lhsAM);
        TypecheckUnit rhs = UnitsUtils.createTypecheckUnit(rhsAM);
        return UnitsUtils.createInternalUnit(division(lhs, rhs));
    }

    public static boolean unitsEqual(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        TypecheckUnit lhs = UnitsUtils.createTypecheckUnit(lhsAM);
        TypecheckUnit rhs = UnitsUtils.createTypecheckUnit(rhsAM);
        return lhs.equals(rhs);
    }
}
