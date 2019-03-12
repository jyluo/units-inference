package units.utils;

import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.javacutil.AnnotationUtils;

/** Utility class with methods for computing the result unit of various arithmetic operations. */
public class UnitsTypecheckUtils {

    /** reference to the units representation utilities library */
    protected final UnitsRepresentationUtils unitsRepUtils;

    public UnitsTypecheckUtils(UnitsRepresentationUtils unitsRepUtils) {
        this.unitsRepUtils = unitsRepUtils;
    }

    public AnnotationMirror addition(
            AnnotatedTypeFactory atf, AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        return atf.getQualifierHierarchy().leastUpperBound(lhsAM, rhsAM);
    }

    public AnnotationMirror subtraction(
            AnnotatedTypeFactory atf, AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        return atf.getQualifierHierarchy().leastUpperBound(lhsAM, rhsAM);
    }

    public AnnotationMirror multiplication(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        TypecheckUnit lhs = unitsRepUtils.createTypecheckUnit(lhsAM);
        TypecheckUnit rhs = unitsRepUtils.createTypecheckUnit(rhsAM);
        return unitsRepUtils.createUnitsRepAnno(multiplication(lhs, rhs));
    }

    private TypecheckUnit multiplication(TypecheckUnit lhs, TypecheckUnit rhs) {
        TypecheckUnit result = new TypecheckUnit(unitsRepUtils);

        // if either lhs or rhs is UnknownUnits, then result is UnknownUnits
        if (lhs.isTop() || rhs.isTop()) {
            result.setUnknownUnits(true);
            return result;
        }

        // if either lhs or rhs is UnitsBottom, then result is UnitsBottom
        if (lhs.isBottom() || rhs.isBottom()) {
            result.setUnitsBottom(true);
            return result;
        }

        // otherwise res component = lhs component + rhs component
        result.setPrefixExponent(lhs.getPrefixExponent() + rhs.getPrefixExponent());
        for (String baseUnit : unitsRepUtils.baseUnits()) {
            result.setExponent(baseUnit, lhs.getExponent(baseUnit) + rhs.getExponent(baseUnit));
        }

        return result;
    }

    public AnnotationMirror division(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        TypecheckUnit lhs = unitsRepUtils.createTypecheckUnit(lhsAM);
        TypecheckUnit rhs = unitsRepUtils.createTypecheckUnit(rhsAM);
        return unitsRepUtils.createUnitsRepAnno(division(lhs, rhs));
    }

    private TypecheckUnit division(TypecheckUnit lhs, TypecheckUnit rhs) {
        TypecheckUnit result = new TypecheckUnit(unitsRepUtils);

        // if either lhs or rhs is UnknownUnits, then result is UnknownUnits
        if (lhs.isTop() || rhs.isTop()) {
            result.setUnknownUnits(true);
            return result;
        }

        // if either lhs or rhs is UnitsBottom, then result is UnitsBottom
        if (lhs.isBottom() || rhs.isBottom()) {
            result.setUnitsBottom(true);
            return result;
        }

        // otherwise res component = lhs component - rhs component
        result.setPrefixExponent(lhs.getPrefixExponent() - rhs.getPrefixExponent());
        for (String baseUnit : unitsRepUtils.baseUnits()) {
            result.setExponent(baseUnit, lhs.getExponent(baseUnit) - rhs.getExponent(baseUnit));
        }

        return result;
    }

    public boolean unitsEqual(AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        TypecheckUnit lhs = unitsRepUtils.createTypecheckUnit(lhsAM);
        TypecheckUnit rhs = unitsRepUtils.createTypecheckUnit(rhsAM);
        return lhs.equals(rhs);
    }

    public boolean unitsComparable(
            AnnotatedTypeFactory atf, AnnotationMirror lhsAM, AnnotationMirror rhsAM) {
        // comparable constraint: lhs <: rhs, or rhs <: lhs
        return atf.getQualifierHierarchy().isSubtype(lhsAM, rhsAM)
                || atf.getQualifierHierarchy().isSubtype(rhsAM, lhsAM);
    }

    public int getIntElementValue(AnnotationMirror anno, CharSequence name) {
        return AnnotationUtils.getElementValue(anno, name, Integer.class, false);
    }
}
