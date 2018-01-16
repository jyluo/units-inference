package units.solvers.backend.z3int.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.SubtypeConstraintEncoder;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.encoder.Z3IntAbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;

public class UnitsZ3IntSubtypeConstraintEncoder
        extends Z3IntAbstractConstraintEncoder<UnitsZ3EncodedSlot, UnitsZ3SolutionSlot>
        implements SubtypeConstraintEncoder<BoolExpr> {

    public UnitsZ3IntSubtypeConstraintEncoder(Lattice lattice, ConstraintVerifier verifier,
            Context ctx,
            Z3IntFormatTranslator<UnitsZ3EncodedSlot, UnitsZ3SolutionSlot> z3IntFormatTranslator) {
        super(lattice, verifier, ctx, z3IntFormatTranslator);
    }

    protected BoolExpr encode(Slot subtype, Slot supertype) {
        return UnitsZ3EncoderUtils.subtype(ctx, subtype.serialize(z3IntFormatTranslator),
                supertype.serialize(z3IntFormatTranslator));
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

    @Override
    public BoolExpr encodeConstant_Constant(ConstantSlot subtype, ConstantSlot supertype) {
        // TODO: need to implement subtype check in real qual hierarchy
        return verifier.isSubtype(subtype, supertype) ? emptyValue : contradictoryValue;
    }
}
