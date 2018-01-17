package units.solvers.backend.z3int.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ternary.SubtractionConstraintEncoder;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.encoder.Z3IntAbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;
import units.internalrepresentation.InferenceUnit;
import units.internalrepresentation.TypecheckUnit;
import units.util.UnitsTypecheckUtils;
import units.util.UnitsZ3EncoderUtils;

public class UnitsZ3IntSubtractionConstraintEncoder
        extends Z3IntAbstractConstraintEncoder<InferenceUnit, TypecheckUnit>
        implements SubtractionConstraintEncoder<BoolExpr> {

    public UnitsZ3IntSubtractionConstraintEncoder(Lattice lattice, ConstraintVerifier verifier,
            Context ctx,
            Z3IntFormatTranslator<InferenceUnit, TypecheckUnit> z3IntFormatTranslator) {
        super(lattice, verifier, ctx, z3IntFormatTranslator);
    }

    // Subtraction between 2 slots resulting in res slot, is encoded as 3 a way equality
    // ie lhs == rhs, and rhs == res.
    protected BoolExpr encode(Slot lhs, Slot rhs, Slot res) {
        return UnitsZ3EncoderUtils.tripleEquality(ctx, lhs.serialize(z3IntFormatTranslator),
                rhs.serialize(z3IntFormatTranslator), res.serialize(z3IntFormatTranslator));
    }

    @Override
    public BoolExpr encodeVariable_Variable(VariableSlot lhs, VariableSlot rhs, VariableSlot res) {
        return encode(lhs, rhs, res);
    }

    @Override
    public BoolExpr encodeVariable_Constant(VariableSlot lhs, ConstantSlot rhs, VariableSlot res) {
        return encode(lhs, rhs, res);
    }

    @Override
    public BoolExpr encodeConstant_Variable(ConstantSlot lhs, VariableSlot rhs, VariableSlot res) {
        return encode(lhs, rhs, res);
    }

    @Override
    public BoolExpr encodeConstant_Constant(ConstantSlot lhs, ConstantSlot rhs, VariableSlot res) {
        // if lhs == rhs, then encode equality between rhs and res
        return UnitsTypecheckUtils.unitsEqual(lhs.getValue(), rhs.getValue())
                ? UnitsZ3EncoderUtils.equality(ctx, rhs.serialize(z3IntFormatTranslator),
                        res.serialize(z3IntFormatTranslator))
                : contradictoryValue;
    }
}
