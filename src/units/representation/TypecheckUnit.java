package units.representation;

import java.util.Map;
import org.checkerframework.javacutil.BugInCF;

/**
 * A data structure class to encapsulate a set of java variables representing a unit for type
 * checking.
 */
public class TypecheckUnit {
    // note: original name is stored but not currently used in toString, hashcode, or equals
    private String originalName;
    private boolean uu;
    private boolean ub;
    private int prefixExponent;
    // Tree map maintaining sorted order on base unit names
    private final Map<String, Integer> exponents;

    public TypecheckUnit() {
        // default originalName value is "default"
        originalName = "default";
        // default UU value is false
        uu = false;
        // default UU value is false
        ub = false;
        // default prefixExponent is 0
        prefixExponent = 0;
        // default exponents are 0
        exponents = UnitsRepresentationUtils.getInstance().createZeroFilledBaseUnitsMap();
    }

    public void setOriginalName(String val) {
        originalName = val;
    }

    public String getOriginalName() {
        return originalName;
    }

    public void setUnknownUnits(boolean val) {
        uu = val;
        // assert !(uu && ub);
    }

    public boolean isUnknownUnits() {
        return uu;
    }

    public void setUnitsBottom(boolean val) {
        ub = val;
        // assert !(uu && ub);
    }

    public boolean isUnitsBottom() {
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
        sb.append(" UU = " + uu);
        sb.append(" UB = " + ub);
        sb.append(" Prefix = " + prefixExponent);
        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            sb.append(" " + baseUnit + " = " + exponents.get(baseUnit));
        }
        return sb.toString();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((exponents == null) ? 0 : exponents.hashCode());
        result = prime * result + prefixExponent;
        result = prime * result + (ub ? 1231 : 1237);
        result = prime * result + (uu ? 1231 : 1237);
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        TypecheckUnit other = (TypecheckUnit) obj;
        if (ub != other.ub) {
            return false;
        }
        if (uu != other.uu) {
            return false;
        }
        if (prefixExponent != other.prefixExponent) {
            return false;
        }
        if (!exponents.equals(other.exponents)) {
            return false;
        }
        return true;
    }
}
