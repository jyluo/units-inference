package units.solvers.backend.gje.representation;

import java.util.Map;
import java.util.Objects;
import units.representation.UnitsRepresentationUtils;

/**
 * A data structure class to encapsulate a set of variables representing a unit for inference
 * through GJE.
 */
public class GJEInferenceUnit {

    private final int cfiSlotID;
    private final int gjeVarID;

    public enum Kind {
        constant,
        variable
    }

    private final Kind kind;

    private boolean uu;
    private boolean ub;
    private int prefixExponent;

    private static final int defaultExponent = 0;

    // Tree map maintaining sorted order on base unit names
    private final Map<String, Integer> exponents;

    private GJEInferenceUnit(int cfiSlotID, int gjeVarID, Kind kind) {
        this.cfiSlotID = cfiSlotID;
        this.gjeVarID = gjeVarID;
        this.kind = kind;

        // default UU value is false
        this.uu = false;
        // default UU value is false
        this.ub = false;
        // default prefixExponent is 0
        this.prefixExponent = defaultExponent;

        exponents = UnitsRepresentationUtils.createSortedBaseUnitMap();

        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            // default exponents are 0
            this.exponents.put(baseUnit, defaultExponent);
        }
    }

    // constants do not have a gje variable ID
    public static GJEInferenceUnit makeConstantSlot(int cfiSlotID) {
        return new GJEInferenceUnit(cfiSlotID, -1, Kind.constant);
    }

    public static GJEInferenceUnit makeVariableSlot(int cfiSlotID, int gjeSlotID) {
        return new GJEInferenceUnit(cfiSlotID, gjeSlotID, Kind.variable);
    }

    public Kind getKind() {
        return kind;
    }

    public boolean isConstant() {
        return kind == Kind.constant;
    }

    public boolean isVariable() {
        return kind == Kind.variable;
    }

    public int getGJEVarID() {
        return gjeVarID;
    }

    public void setUnknownUnits(boolean val) {
        uu = val;
    }

    public boolean getUnknownUnits() {
        return uu;
    }

    public void setUnitsBottom(boolean val) {
        ub = val;
    }

    public boolean getUnitsBottom() {
        return ub;
    }

    public void setPrefixExponent(int exp) {
        prefixExponent = exp;
    }

    public int getPrefixExponent() {
        return prefixExponent;
    }

    public void setExponent(String unit, int exp) {
        assert exponents.containsKey(unit);
        exponents.replace(unit, exp);
    }

    public int getExponent(String unit) {
        assert exponents.containsKey(unit);
        return exponents.get(unit);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("slot ");
        sb.append(cfiSlotID);
        sb.append(" : UU = " + uu);
        sb.append(" UB = " + ub);
        sb.append(" Prefix = " + prefixExponent);
        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            sb.append(" " + baseUnit + " = " + exponents.get(baseUnit));
        }
        return sb.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(cfiSlotID, kind, uu, ub, prefixExponent, exponents);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        GJEInferenceUnit other = (GJEInferenceUnit) obj;
        if (cfiSlotID != other.cfiSlotID) return false;
        if (exponents == null) {
            if (other.exponents != null) return false;
        } else if (!exponents.equals(other.exponents)) return false;
        if (kind != other.kind) return false;
        if (prefixExponent != other.prefixExponent) return false;
        if (ub != other.ub) return false;
        if (uu != other.uu) return false;
        return true;
    }
}
