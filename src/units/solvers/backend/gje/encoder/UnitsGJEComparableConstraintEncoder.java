package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import units.representation.TypecheckUnit;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsGJEComparableConstraintEncoder
        extends GJEAbstractConstraintEncoder<Z3InferenceUnit, TypecheckUnit>
        implements ComparableConstraintEncoder<BoolExpr> {

    public UnitsGJEComparableConstraintEncoder(
            Lattice lattice,
            Context ctx,
            GJEFormatTranslator<Z3InferenceUnit, TypecheckUnit> z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    protected BoolExpr encode(Slot fst, Slot snd) {
        Z3InferenceUnit first = fst.serialize(gjeFormatTranslator);
        Z3InferenceUnit second = snd.serialize(gjeFormatTranslator);

        // fst <: snd or snd <: fst
        return ctx.mkOr(
                UnitsGJEEncoderUtils.subtype(ctx, first, second),
                UnitsGJEEncoderUtils.subtype(ctx, second, first));
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
