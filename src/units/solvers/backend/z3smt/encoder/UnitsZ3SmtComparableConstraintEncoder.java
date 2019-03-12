package units.solvers.backend.z3smt.encoder;

import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import units.solvers.backend.z3smt.UnitsZ3SmtFormatTranslator;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsZ3SmtComparableConstraintEncoder extends UnitsZ3SmtAbstractConstraintEncoder
        implements ComparableConstraintEncoder<BoolExpr> {

    public UnitsZ3SmtComparableConstraintEncoder(
            Lattice lattice, Context ctx, UnitsZ3SmtFormatTranslator unitsZ3SmtFormatTranslator) {
        super(lattice, ctx, unitsZ3SmtFormatTranslator);
    }

    protected BoolExpr encode(Slot fst, Slot snd) {
        Z3InferenceUnit first = fst.serialize(z3SmtFormatTranslator);
        Z3InferenceUnit second = snd.serialize(z3SmtFormatTranslator);

        // fst <: snd or snd <: fst
        return ctx.mkOr(
                unitsZ3SmtEncoderUtils.subtype(ctx, first, second),
                unitsZ3SmtEncoderUtils.subtype(ctx, second, first));
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
