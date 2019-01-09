package units.solvers.backend.z3smt.encoder;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.encoder.Z3SmtAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.Context;
import units.representation.TypecheckUnit;
import units.solvers.backend.z3smt.representation.Z3EquationSet;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsZ3SmtComparableConstraintEncoder
        extends Z3SmtAbstractConstraintEncoder<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
        implements ComparableConstraintEncoder<Z3EquationSet> {

    public UnitsZ3SmtComparableConstraintEncoder(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
                    z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    protected Z3EquationSet encode(Slot fst, Slot snd) {
        Z3InferenceUnit first = fst.serialize(z3SmtFormatTranslator);
        Z3InferenceUnit second = snd.serialize(z3SmtFormatTranslator);

        return UnitsZ3SmtEncoderUtils.comparable(ctx, first, second);
    }

    @Override
    public Z3EquationSet encodeVariable_Variable(VariableSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public Z3EquationSet encodeVariable_Constant(VariableSlot fst, ConstantSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public Z3EquationSet encodeConstant_Variable(ConstantSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }
}
