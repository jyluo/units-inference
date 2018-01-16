package units.solvers.backend.z3int.encoder;

import java.util.HashMap;
import java.util.Map;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import units.util.UnitsUtils;

/**
 * A data structure class to encapsulate a set of Z3 variables representing an encoded constant or
 * variable slot, and in turn a unit.
 */
public class UnitsZ3EncodedSlot {
    private final Context ctx;
    private final int slotID;

    private BoolExpr uu;
    private BoolExpr ub;

    private IntExpr prefixExponent;

    private final Map<String, IntExpr> exponents;

    private UnitsZ3EncodedSlot(Context ctx, int slotID) {
        this.ctx = ctx;
        this.slotID = slotID;
        exponents = new HashMap<>();
    }

    public static UnitsZ3EncodedSlot makeConstantSlot(Context ctx, int slotID) {
        UnitsZ3EncodedSlot slot = new UnitsZ3EncodedSlot(ctx, slotID);

        // default UU value is false
        slot.uu = ctx.mkBool(false);
        // default UU value is false
        slot.ub = ctx.mkBool(false);
        // default prefixExponent is 0
        slot.prefixExponent = ctx.mkInt(0);

        for (String baseUnit : UnitsUtils.baseUnits()) {
            // default exponents are 0
            slot.exponents.put(baseUnit, ctx.mkInt(0));
        }

        return slot;
    }

    public static UnitsZ3EncodedSlot makeVariableSlot(Context ctx, int slotID) {
        UnitsZ3EncodedSlot slot = new UnitsZ3EncodedSlot(ctx, slotID);

        slot.uu = ctx.mkBoolConst(UnitsUtils.z3VarName(slotID, UnitsUtils.uuSlotName));
        slot.ub = ctx.mkBoolConst(UnitsUtils.z3VarName(slotID, UnitsUtils.ubSlotName));
        slot.prefixExponent =
                ctx.mkIntConst(UnitsUtils.z3VarName(slotID, UnitsUtils.prefixSlotName));

        for (String baseUnit : UnitsUtils.baseUnits()) {
            slot.exponents.put(baseUnit, ctx.mkIntConst(UnitsUtils.z3VarName(slotID, baseUnit)));
        }

        return slot;
    }

    public void setUnknownUnits(boolean val) {
        uu = ctx.mkBool(val);
    }

    public BoolExpr getUnknownUnits() {
        return uu;
    }

    public void setUnitsBottom(boolean val) {
        ub = ctx.mkBool(val);
    }

    public BoolExpr getUnitsBottom() {
        return ub;
    }

    public void setPrefixExponent(int exp) {
        prefixExponent = ctx.mkInt(exp);
    }

    public IntExpr getPrefixExponent() {
        return prefixExponent;
    }

    public void setExponent(String unit, int exp) {
        assert exponents.containsKey(unit);
        exponents.replace(unit, ctx.mkInt(exp));
    }

    public IntExpr getExponent(String unit) {
        assert exponents.containsKey(unit);
        return exponents.get(unit);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("slot ");
        sb.append(slotID);
        sb.append(" : UU = " + uu.toString());
        sb.append(" UB = " + ub.toString());
        sb.append(" Prefix = " + prefixExponent.toString());
        for (String baseUnit : UnitsUtils.baseUnits()) {
            sb.append(" " + baseUnit + " = " + exponents.get(baseUnit));
        }
        return sb.toString();
    }

    @Override
    public int hashCode() {
        final int prime = 41;
        int result = 1;
        result = prime * result + ((exponents == null) ? 0 : exponents.hashCode());
        result = prime * result + ((prefixExponent == null) ? 0 : prefixExponent.hashCode());
        result = prime * result + slotID;
        result = prime * result + ((ub == null) ? 0 : ub.hashCode());
        result = prime * result + ((uu == null) ? 0 : uu.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        UnitsZ3EncodedSlot other = (UnitsZ3EncodedSlot) obj;
        if (exponents == null) {
            if (other.exponents != null)
                return false;
        } else if (!exponents.equals(other.exponents))
            return false;
        if (prefixExponent == null) {
            if (other.prefixExponent != null)
                return false;
        } else if (!prefixExponent.equals(other.prefixExponent))
            return false;
        if (slotID != other.slotID)
            return false;
        if (ub == null) {
            if (other.ub != null)
                return false;
        } else if (!ub.equals(other.ub))
            return false;
        if (uu == null) {
            if (other.uu != null)
                return false;
        } else if (!uu.equals(other.uu))
            return false;
        return true;
    }
}
