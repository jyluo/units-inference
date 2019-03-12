package units.solvers.backend.z3smt.encoder;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.encoder.Z3SmtAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;
import units.utils.TypecheckUnit;

public class UnitsZ3SmtEqualityConstraintEncoder
        extends Z3SmtAbstractConstraintEncoder<Z3InferenceUnit, TypecheckUnit>
        implements EqualityConstraintEncoder<BoolExpr> {

    public UnitsZ3SmtEqualityConstraintEncoder(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<Z3InferenceUnit, TypecheckUnit> z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    // 2 Slots are equal if their components are equal
    protected BoolExpr encode(Slot fst, Slot snd) {
        return UnitsZ3SmtEncoderUtils.equality(
                ctx, fst.serialize(z3SmtFormatTranslator), snd.serialize(z3SmtFormatTranslator));
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
