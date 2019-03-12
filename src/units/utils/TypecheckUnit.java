package units.utils;

import java.util.Map;
import java.util.Objects;
import org.checkerframework.javacutil.BugInCF;

/**
 * A data structure class to encapsulate a set of java variables representing a unit for type
 * checking.
 */
public class TypecheckUnit {
    /** reference to the units representation utilities library */
    protected final UnitsRepresentationUtils unitsRepUtils;

    private boolean uu;
    private boolean ub;
    private int prefixExponent;
    // Tree map maintaining sorted order on base unit names
    private final Map<String, Integer> exponents;

    public TypecheckUnit(UnitsRepresentationUtils unitsRepUtils) {
        this.unitsRepUtils = unitsRepUtils;

        // default UU value is false
        uu = false;
        // default UU value is false
        ub = false;
        // default prefixExponent is 0
        prefixExponent = 0;
        // default exponents are 0
        exponents = unitsRepUtils.createZeroFilledBaseUnitsMap();
    }

    public void setUnknownUnits(boolean val) {
        if (uu && ub) {
            throw new BugInCF("Cannot set top and bottom both to true at the same time");
        }
        uu = val;
    }

    public boolean isTop() {
        return uu;
    }

    public void setUnitsBottom(boolean val) {
        if (uu && ub) {
            throw new BugInCF("Cannot set top and bottom both to true at the same time");
        }
        ub = val;
    }

    public boolean isBottom() {
        return ub;
    }

    public void setPrefixExponent(int exp) {
        prefixExponent = exp;
    }

    public int getPrefixExponent() {
        return prefixExponent;
    }

    public void setExponent(String unit, int exp) {
        if (!exponents.containsKey(unit)) {
            // return; // for pure performance experiment
            throw new BugInCF("Inserting exponent for base unit " + unit + " which does not exist");
        }
        exponents.replace(unit, exp);
    }

    public int getExponent(String unit) {
        if (!exponents.containsKey(unit)) {
            // return 0; // for pure performance experiment
            throw new BugInCF("Getting exponent for base unit " + unit + " which does not exist");
        }
        return exponents.get(unit);
    }

    public Map<String, Integer> getExponents() {
        return exponents;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("UU = " + uu);
        sb.append(" UB = " + ub);
        sb.append(" Base-10-Prefix = " + prefixExponent);
        for (String baseUnit : unitsRepUtils.baseUnits()) {
            sb.append(" " + baseUnit + " = " + exponents.get(baseUnit));
        }
        return sb.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(this.getClass().getCanonicalName(), uu, ub, prefixExponent, exponents);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null || getClass() != obj.getClass()) {
            return false;
        }
        TypecheckUnit other = (TypecheckUnit) obj;
        return uu == other.uu
                && ub == other.ub
                && prefixExponent == other.prefixExponent
                && exponents.equals(other.exponents);
    }
}
