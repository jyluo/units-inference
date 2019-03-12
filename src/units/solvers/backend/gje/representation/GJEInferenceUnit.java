package units.solvers.backend.gje.representation;

import java.util.Map;
import java.util.Objects;
import units.utils.UnitsRepresentationUtils;

/**
 * A data structure class to encapsulate a set of variables representing a unit for inference
 * through GJE.
 */
public class GJEInferenceUnit {
    /** reference to the units representation utilities library */
    protected final UnitsRepresentationUtils unitsRepUtils;

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

    private GJEInferenceUnit(
            UnitsRepresentationUtils unitsRepUtils, int cfiSlotID, int gjeVarID, Kind kind) {
        this.unitsRepUtils = unitsRepUtils;

        this.cfiSlotID = cfiSlotID;
        this.gjeVarID = gjeVarID;
        this.kind = kind;

        // default UU value is false
        this.uu = false;
        // default UU value is false
        this.ub = false;
        // default prefixExponent is 0
        this.prefixExponent = defaultExponent;

        exponents = unitsRepUtils.createSortedBaseUnitMap();

        for (String baseUnit : unitsRepUtils.baseUnits()) {
            // default exponents are 0
            this.exponents.put(baseUnit, defaultExponent);
        }
    }

    // constants do not have a gje variable ID
    public static GJEInferenceUnit makeConstantSlot(
            UnitsRepresentationUtils unitsRepUtils, int cfiSlotID) {
        return new GJEInferenceUnit(unitsRepUtils, cfiSlotID, -1, Kind.constant);
    }

    public static GJEInferenceUnit makeVariableSlot(
            UnitsRepresentationUtils unitsRepUtils, int cfiSlotID, int gjeSlotID) {
        return new GJEInferenceUnit(unitsRepUtils, cfiSlotID, gjeSlotID, Kind.variable);
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
        sb.append(" Base-10-Prefix = " + prefixExponent);
        for (String baseUnit : unitsRepUtils.baseUnits()) {
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
        if (this == obj) {
            return true;
        }
        if (obj == null || getClass() != obj.getClass()) {
            return false;
        }
        GJEInferenceUnit other = (GJEInferenceUnit) obj;
        return cfiSlotID == other.cfiSlotID
                && kind == other.kind
                && uu == other.uu
                && ub == other.ub
                && prefixExponent == other.prefixExponent
                && exponents.equals(other.exponents);
    }
}
