package units.solvers.backend.z3smt.encoder;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.encoder.Z3SmtAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.SubtypeConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.Context;
import units.representation.TypecheckUnit;
import units.solvers.backend.z3smt.representation.Z3EquationSet;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsZ3SmtSubtypeConstraintEncoder
        extends Z3SmtAbstractConstraintEncoder<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
        implements SubtypeConstraintEncoder<Z3EquationSet> {

    public UnitsZ3SmtSubtypeConstraintEncoder(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
                    z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    protected Z3EquationSet encode(Slot subtype, Slot supertype) {
        return UnitsZ3SmtEncoderUtils.subtype(
                ctx,
                subtype.serialize(z3SmtFormatTranslator),
                supertype.serialize(z3SmtFormatTranslator));
    }

    @Override
    public Z3EquationSet encodeVariable_Variable(VariableSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public Z3EquationSet encodeVariable_Constant(VariableSlot subtype, ConstantSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public Z3EquationSet encodeConstant_Variable(ConstantSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }
}
