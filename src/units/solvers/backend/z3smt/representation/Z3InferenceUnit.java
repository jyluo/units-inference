package units.solvers.backend.z3smt.representation;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import java.lang.annotation.Annotation;
import java.util.Map;
import units.representation.UnitsRepresentationUtils;
import units.solvers.backend.z3smt.encoder.UnitsZ3SmtEncoderUtils;

/**
 * A data structure class to encapsulate a set of Z3 variables representing a unit for inference.
 */
public class Z3InferenceUnit {
    private final Context ctx;
    private final int slotID;

    private BoolExpr uu;
    private BoolExpr ub;
    private IntExpr prefixExponent;
    // Tree map maintaining sorted order on base unit names
    private final Map<Class<? extends Annotation>, IntExpr> exponents;

    // helper constant
    private final IntNum intZero;

    private Z3InferenceUnit(Context ctx, int slotID) {
        this.ctx = ctx;
        this.slotID = slotID;
        exponents = UnitsRepresentationUtils.createSortedAnnotationClassLiteralMap();
        intZero = ctx.mkInt(0);
    }

    public static Z3InferenceUnit makeConstantSlot(Context ctx, int slotID) {
        Z3InferenceUnit slot = new Z3InferenceUnit(ctx, slotID);

        // default UU value is false
        slot.uu = ctx.mkBool(false);
        // default UU value is false
        slot.ub = ctx.mkBool(false);
        // default prefixExponent is 0
        slot.prefixExponent = slot.intZero;

        for (Class<? extends Annotation> baseUnit :
                UnitsRepresentationUtils.getInstance().baseUnits()) {
            // default exponents are 0
            slot.exponents.put(baseUnit, slot.intZero);
        }

        return slot;
    }

    public static Z3InferenceUnit makeVariableSlot(Context ctx, int slotID) {
        Z3InferenceUnit slot = new Z3InferenceUnit(ctx, slotID);

        slot.uu =
                ctx.mkBoolConst(
                        UnitsZ3SmtEncoderUtils.z3VarName(
                                slotID, UnitsZ3SmtEncoderUtils.uuSlotName));
        slot.ub =
                ctx.mkBoolConst(
                        UnitsZ3SmtEncoderUtils.z3VarName(
                                slotID, UnitsZ3SmtEncoderUtils.ubSlotName));
        slot.prefixExponent =
                ctx.mkIntConst(
                        UnitsZ3SmtEncoderUtils.z3VarName(
                                slotID, UnitsZ3SmtEncoderUtils.prefixSlotName));

        for (Class<? extends Annotation> baseUnit :
                UnitsRepresentationUtils.getInstance().baseUnits()) {
            slot.exponents.put(
                    baseUnit,
                    ctx.mkIntConst(
                            UnitsZ3SmtEncoderUtils.z3VarName(slotID, baseUnit.getSimpleName())));
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

    public void setExponent(Class<? extends Annotation> unit, int exp) {
        assert exponents.containsKey(unit);
        exponents.replace(unit, ctx.mkInt(exp));
    }

    public IntExpr getExponent(Class<? extends Annotation> unit) {
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
        for (Class<? extends Annotation> baseUnit :
                UnitsRepresentationUtils.getInstance().baseUnits()) {
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
        Z3InferenceUnit other = (Z3InferenceUnit) obj;
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
