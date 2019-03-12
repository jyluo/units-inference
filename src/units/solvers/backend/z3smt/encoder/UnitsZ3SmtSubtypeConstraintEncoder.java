package units.solvers.backend.z3smt.encoder;

import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.SubtypeConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import units.solvers.backend.z3smt.UnitsZ3SmtFormatTranslator;

public class UnitsZ3SmtSubtypeConstraintEncoder extends UnitsZ3SmtAbstractConstraintEncoder
        implements SubtypeConstraintEncoder<BoolExpr> {

    public UnitsZ3SmtSubtypeConstraintEncoder(
            Lattice lattice, Context ctx, UnitsZ3SmtFormatTranslator unitsZ3SmtFormatTranslator) {
        super(lattice, ctx, unitsZ3SmtFormatTranslator);
    }

    protected BoolExpr encode(Slot subtype, Slot supertype) {
        return unitsZ3SmtEncoderUtils.subtype(
                ctx,
                subtype.serialize(z3SmtFormatTranslator),
                supertype.serialize(z3SmtFormatTranslator));
    }

    @Override
    public BoolExpr encodeVariable_Variable(VariableSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public BoolExpr encodeVariable_Constant(VariableSlot subtype, ConstantSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public BoolExpr encodeConstant_Variable(ConstantSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }
}
