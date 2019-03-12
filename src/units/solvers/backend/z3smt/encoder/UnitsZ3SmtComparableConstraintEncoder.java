package units.solvers.backend.z3smt.encoder;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.encoder.Z3SmtAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;
import units.utils.TypecheckUnit;

public class UnitsZ3SmtComparableConstraintEncoder
        extends Z3SmtAbstractConstraintEncoder<Z3InferenceUnit, TypecheckUnit>
        implements ComparableConstraintEncoder<BoolExpr> {

    public UnitsZ3SmtComparableConstraintEncoder(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<Z3InferenceUnit, TypecheckUnit> z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    protected BoolExpr encode(Slot fst, Slot snd) {
        Z3InferenceUnit first = fst.serialize(z3SmtFormatTranslator);
        Z3InferenceUnit second = snd.serialize(z3SmtFormatTranslator);

        // fst <: snd or snd <: fst
        return ctx.mkOr(
                UnitsZ3SmtEncoderUtils.subtype(ctx, first, second),
                UnitsZ3SmtEncoderUtils.subtype(ctx, second, first));
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
