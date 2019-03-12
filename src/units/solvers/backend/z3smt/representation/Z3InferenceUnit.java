package units.solvers.backend.z3smt.representation;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import java.util.Map;
import java.util.Objects;
import units.solvers.backend.z3smt.encoder.UnitsZ3SmtEncoderUtils;
import units.utils.UnitsInferenceRepresentationUtils;

/**
 * A data structure class to encapsulate a set of Z3 variables representing a unit for inference.
 */
public class Z3InferenceUnit {
    /** reference to the units representation utilities library */
    private final UnitsInferenceRepresentationUtils unitsRepUtils;

    // TODO: long term clean up, strip out the use of z3 Java API and construct raw
    // strings for each of the variables?
    private final Context ctx;
    private final int slotID;

    private BoolExpr uu;
    private BoolExpr ub;
    private IntExpr prefixExponent;
    // Tree map maintaining sorted order on base unit names
    private final Map<String, IntExpr> exponents;

    // helper constant
    private final IntNum intZero;

    private Z3InferenceUnit(
            UnitsInferenceRepresentationUtils unitsRepUtils, Context ctx, int slotID) {
        this.unitsRepUtils = unitsRepUtils;
        this.ctx = ctx;
        this.slotID = slotID;
        exponents = unitsRepUtils.createSortedBaseUnitMap();
        intZero = ctx.mkInt(0);
    }

    public static Z3InferenceUnit makeConstantSlot(
            UnitsInferenceRepresentationUtils unitsRepUtils, Context ctx, int slotID) {
        Z3InferenceUnit slot = new Z3InferenceUnit(unitsRepUtils, ctx, slotID);

        // default UU value is false
        slot.uu = ctx.mkBool(false);
        // default UU value is false
        slot.ub = ctx.mkBool(false);
        // default prefixExponent is 0
        slot.prefixExponent = slot.intZero;

        for (String baseUnit : unitsRepUtils.serializableBaseUnits()) {
            // default exponents are 0
            slot.exponents.put(baseUnit, slot.intZero);
        }

        return slot;
    }

    public static Z3InferenceUnit makeVariableSlot(
            UnitsInferenceRepresentationUtils unitsRepUtils,
            UnitsZ3SmtEncoderUtils unitsZ3SmtEncoderUtils,
            Context ctx,
            int slotID) {
        Z3InferenceUnit slot = new Z3InferenceUnit(unitsRepUtils, ctx, slotID);

        slot.uu =
                ctx.mkBoolConst(
                        unitsZ3SmtEncoderUtils.z3VarName(
                                slotID, UnitsZ3SmtEncoderUtils.uuSlotName));
        slot.ub =
                ctx.mkBoolConst(
                        unitsZ3SmtEncoderUtils.z3VarName(
                                slotID, UnitsZ3SmtEncoderUtils.ubSlotName));
        slot.prefixExponent =
                ctx.mkIntConst(
                        unitsZ3SmtEncoderUtils.z3VarName(
                                slotID, UnitsZ3SmtEncoderUtils.prefixSlotName));

        for (String baseUnit : unitsRepUtils.serializableBaseUnits()) {
            slot.exponents.put(
                    baseUnit, ctx.mkIntConst(unitsZ3SmtEncoderUtils.z3VarName(slotID, baseUnit)));
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
        sb.append(" Base-10-Prefix = " + prefixExponent.toString());
        for (String baseUnit : unitsRepUtils.serializableBaseUnits()) {
            sb.append(" " + baseUnit + " = " + exponents.get(baseUnit));
        }
        // TODO: printout unused base units?
        return sb.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(slotID, uu, ub, prefixExponent, exponents);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null || getClass() != obj.getClass()) {
            return false;
        }
        Z3InferenceUnit other = (Z3InferenceUnit) obj;
        return slotID == other.slotID
                && uu.equals(other.uu)
                && ub.equals(other.ub)
                && prefixExponent.equals(other.prefixExponent)
                && exponents.equals(other.exponents);
    }
}
