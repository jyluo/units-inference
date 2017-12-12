package units.solvers.backend.z3int.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.encoder.Z3IntAbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;
import units.util.UnitsUtils;

public class UnitsZ3IntEqualityConstraintEncoder
        extends Z3IntAbstractConstraintEncoder<UnitsZ3EncodedSlot, UnitsZ3EncodedSlot>
        implements EqualityConstraintEncoder<BoolExpr> {

    public UnitsZ3IntEqualityConstraintEncoder(Lattice lattice, ConstraintVerifier verifier,
            Context ctx,
            Z3IntFormatTranslator<UnitsZ3EncodedSlot, UnitsZ3EncodedSlot> z3IntFormatTranslator) {
        super(lattice, verifier, ctx, z3IntFormatTranslator);
    }

    // fst = snd iff the bool and int component values are equal
    protected BoolExpr encode(Slot fst, Slot snd) {
        UnitsZ3EncodedSlot fstESlot = fst.serialize(z3IntFormatTranslator);
        UnitsZ3EncodedSlot sndESlot = snd.serialize(z3IntFormatTranslator);

        BoolExpr result =
                ctx.mkAnd(ctx.mkEq(fstESlot.getUnknownUnits(), sndESlot.getUnknownUnits()),
                        ctx.mkEq(fstESlot.getUnitsBottom(), sndESlot.getUnitsBottom()),
                        ctx.mkEq(fstESlot.getPrefixExponent(), sndESlot.getPrefixExponent()));
        for (String baseUnit : UnitsUtils.baseUnits()) {
            result = ctx.mkAnd(result,
                    ctx.mkEq(fstESlot.getExponent(baseUnit), sndESlot.getExponent(baseUnit)));
        }
        return result;
    }

    @Override
    public BoolExpr encodeVariable_Variable(VariableSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public BoolExpr encodeVariable_Constant(VariableSlot fst, ConstantSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public BoolExpr encodeConstant_Variable(ConstantSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public BoolExpr encodeConstant_Constant(ConstantSlot fst, ConstantSlot snd) {
        return verifier.areEqual(fst, snd) ? emptyValue : contradictoryValue;
    }
}
