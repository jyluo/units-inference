package units.representation;

import java.util.Map;
import java.util.TreeMap;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import units.util.UnitsZ3SmtEncoderUtils;

/**
 * A data structure class to encapsulate a set of Z3 variables representing a unit for inference.
 */
public class InferenceUnit {
    private final Context ctx;
    private final int slotID;

    private BoolExpr uu;
    private BoolExpr ub;
    private IntExpr prefixExponent;
    // Tree map maintaining sorted order on base unit names
    private final Map<String, IntExpr> exponents;

    // helper constant
    private final IntNum intZero;

    private InferenceUnit(Context ctx, int slotID) {
        this.ctx = ctx;
        this.slotID = slotID;
        exponents = new TreeMap<>();
        intZero = ctx.mkInt(0);
    }

    public static InferenceUnit makeConstantSlot(Context ctx, int slotID) {
        InferenceUnit slot = new InferenceUnit(ctx, slotID);

        // default UU value is false
        slot.uu = ctx.mkBool(false);
        // default UU value is false
        slot.ub = ctx.mkBool(false);
        // default prefixExponent is 0
        slot.prefixExponent = slot.intZero;

        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            // default exponents are 0
            slot.exponents.put(baseUnit, slot.intZero);
        }

        return slot;
    }

    public static InferenceUnit makeVariableSlot(Context ctx, int slotID) {
        InferenceUnit slot = new InferenceUnit(ctx, slotID);

        slot.uu = ctx.mkBoolConst(
                UnitsZ3SmtEncoderUtils.z3VarName(slotID, UnitsZ3SmtEncoderUtils.uuSlotName));
        slot.ub = ctx.mkBoolConst(
                UnitsZ3SmtEncoderUtils.z3VarName(slotID, UnitsZ3SmtEncoderUtils.ubSlotName));
        slot.prefixExponent = ctx.mkIntConst(
                UnitsZ3SmtEncoderUtils.z3VarName(slotID, UnitsZ3SmtEncoderUtils.prefixSlotName));

        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            slot.exponents.put(baseUnit,
                    ctx.mkIntConst(UnitsZ3SmtEncoderUtils.z3VarName(slotID, baseUnit)));
        }

        return slot;
    }

    /**
     * Well-formness constraint: that either uu = true, ub = true, or uu == ub = false
     */
    public BoolExpr getWellformnessConstraint() {
        BoolExpr dimensionlessConstraint = constraintUnitToBeDimensionless();
        /* @formatter:off // this is for eclipse formatter */
        return UnitsZ3SmtEncoderUtils.mkChainXor(ctx,
                ctx.mkAnd(ctx.mkNot(uu), ctx.mkNot(ub)),
                ctx.mkAnd(uu, dimensionlessConstraint),
                ctx.mkAnd(ub, dimensionlessConstraint));
        /* @formatter:on // this is for eclipse formatter */
    }

    private BoolExpr constraintUnitToBeDimensionless() {
        BoolExpr result = ctx.mkEq(prefixExponent, ctx.mkInt(0));
        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            /* @formatter:off // this is for eclipse formatter */
            result = ctx.mkAnd(result,
                ctx.mkEq(getExponent(baseUnit), intZero)
            );
            /* @formatter:on // this is for eclipse formatter */
        }
        return result;
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
        result = prime * result + ((prefixExponent == null) ? 0 : prefixExponent.hashCode());
        result = prime * result + slotID;
        result = prime * result + ((ub == null) ? 0 : ub.hashCode());
        result = prime * result + ((uu == null) ? 0 : uu.hashCode());
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
        InferenceUnit other = (InferenceUnit) obj;
        if (exponents == null) {
            if (other.exponents != null) {
                return false;
            }
        } else if (!exponents.equals(other.exponents)) {
            return false;
        }
        if (prefixExponent == null) {
            if (other.prefixExponent != null) {
                return false;
            }
        } else if (!prefixExponent.equals(other.prefixExponent)) {
            return false;
        }
        if (slotID != other.slotID) {
            return false;
        }
        if (ub == null) {
            if (other.ub != null) {
                return false;
            }
        } else if (!ub.equals(other.ub)) {
            return false;
        }
        if (uu == null) {
            if (other.uu != null) {
                return false;
            }
        } else if (!uu.equals(other.uu)) {
            return false;
        }
        return true;
    }

}
