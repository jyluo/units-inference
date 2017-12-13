package units.solvers.backend.z3int.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ternary.MultiplicationConstraintEncoder;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.encoder.Z3IntAbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;

public class UnitsZ3IntMultiplicationConstraintEncoder
        extends Z3IntAbstractConstraintEncoder<UnitsZ3EncodedSlot, UnitsZ3SolutionSlot>
        implements MultiplicationConstraintEncoder<BoolExpr> {

    public UnitsZ3IntMultiplicationConstraintEncoder(Lattice lattice, ConstraintVerifier verifier,
            Context ctx,
            Z3IntFormatTranslator<UnitsZ3EncodedSlot, UnitsZ3SolutionSlot> z3IntFormatTranslator) {
        super(lattice, verifier, ctx, z3IntFormatTranslator);
    }

    // Multiplication between 2 slots resulting in res slot, is the sum of the component exponents
    // unless either lhs or rhs is UnknownUnits or UnitsBottom, for which then the result is always
    // UnknownUnits
    protected BoolExpr encode(Slot lhs, Slot rhs, Slot res) {
        return UnitsZ3EncoderUtils.multiply(ctx, lhs.serialize(z3IntFormatTranslator),
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
        // encode equality between result of multiplication and res
        // TODO: create computeable multiply method
        // return UnitsZ3EncoderUtils.equality(ctx, rhs.serialize(z3IntFormatTranslator),
        // res.serialize(z3IntFormatTranslator));
        return emptyValue;
    }
}
