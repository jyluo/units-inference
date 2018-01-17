package units.solvers.backend.z3int.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ternary.ModulusConstraintEncoder;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.encoder.Z3IntAbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;
import units.internalrepresentation.InferenceUnit;
import units.internalrepresentation.TypecheckUnit;
import units.util.UnitsZ3EncoderUtils;

public class UnitsZ3IntModulusConstraintEncoder
        extends Z3IntAbstractConstraintEncoder<InferenceUnit, TypecheckUnit>
        implements ModulusConstraintEncoder<BoolExpr> {

    public UnitsZ3IntModulusConstraintEncoder(Lattice lattice, ConstraintVerifier verifier,
            Context ctx,
            Z3IntFormatTranslator<InferenceUnit, TypecheckUnit> z3IntFormatTranslator) {
        super(lattice, verifier, ctx, z3IntFormatTranslator);
    }

    // Modulus between 2 slots resulting in res slot, is always an equality between lhs and res
    // slots
    protected BoolExpr encode(Slot lhs, Slot rhs, Slot res) {
        return UnitsZ3EncoderUtils.equality(ctx, lhs.serialize(z3IntFormatTranslator),
                res.serialize(z3IntFormatTranslator));
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
        return encode(lhs, rhs, res);
    }
}
