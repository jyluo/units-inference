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
        extends Z3IntAbstractConstraintEncoder<UnitsZ3EncodedSlot, UnitsZ3EncodedSlot>
        implements SubtypeConstraintEncoder<BoolExpr> {

    public UnitsZ3IntSubtypeConstraintEncoder(Lattice lattice, ConstraintVerifier verifier,
            Context ctx,
            Z3IntFormatTranslator<UnitsZ3EncodedSlot, UnitsZ3EncodedSlot> z3IntFormatTranslator) {
        super(lattice, verifier, ctx, z3IntFormatTranslator);
    }

    // fornow very hacky
    // subtype <: supertype if int value of subtype <= supertype
    protected BoolExpr encode(Slot subtype, Slot supertype) {
        UnitsZ3EncodedSlot subtypeInt = subtype.serialize(z3IntFormatTranslator);
        UnitsZ3EncodedSlot supertypeInt = supertype.serialize(z3IntFormatTranslator);

        return null; // context.mkLe(subtypeInt, supertypeInt);
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
        return verifier.isSubtype(subtype, supertype) ? emptyValue : contradictoryValue;
    }
}
