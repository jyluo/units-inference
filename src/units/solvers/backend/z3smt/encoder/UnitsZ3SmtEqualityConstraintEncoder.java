package units.solvers.backend.z3smt.encoder;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.encoder.Z3SmtAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.Context;
import units.representation.TypecheckUnit;
import units.solvers.backend.z3smt.representation.Z3EquationSet;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsZ3SmtEqualityConstraintEncoder
        extends Z3SmtAbstractConstraintEncoder<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
        implements EqualityConstraintEncoder<Z3EquationSet> {

    public UnitsZ3SmtEqualityConstraintEncoder(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
                    z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    // 2 Slots are equal if their components are equal
    protected Z3EquationSet encode(Slot fst, Slot snd) {
        return UnitsZ3SmtEncoderUtils.equality(
                ctx, fst.serialize(z3SmtFormatTranslator), snd.serialize(z3SmtFormatTranslator));
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
