package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import units.representation.InferenceUnit;
import units.representation.TypecheckUnit;
import units.util.UnitsGJEEncoderUtils;

public class UnitsGJEEqualityConstraintEncoder
        extends GJEAbstractConstraintEncoder<InferenceUnit, TypecheckUnit>
        implements EqualityConstraintEncoder<BoolExpr> {

    public UnitsGJEEqualityConstraintEncoder(
            Lattice lattice,
            Context ctx,
            GJEFormatTranslator<InferenceUnit, TypecheckUnit> z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    // 2 Slots are equal if their components are equal
    protected BoolExpr encode(Slot fst, Slot snd) {
        return UnitsGJEEncoderUtils.equality(
                ctx, fst.serialize(gjeFormatTranslator), snd.serialize(gjeFormatTranslator));
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
}
