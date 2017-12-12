package units.solvers.backend.z3int.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ternary.AdditionConstraintEncoder;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.encoder.Z3IntAbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;

public class UnitsZ3IntAdditionConstraintEncoder
        extends Z3IntAbstractConstraintEncoder<UnitsZ3EncodedSlot, UnitsZ3EncodedSlot>
        implements AdditionConstraintEncoder<BoolExpr> {

    public UnitsZ3IntAdditionConstraintEncoder(Lattice lattice, ConstraintVerifier verifier,
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
    public BoolExpr encodeVariable_Variable(VariableSlot lhs, VariableSlot rhs,
            VariableSlot result) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public BoolExpr encodeVariable_Constant(VariableSlot lhs, ConstantSlot rhs,
            VariableSlot result) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public BoolExpr encodeConstant_Variable(ConstantSlot lhs, VariableSlot rhs,
            VariableSlot result) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public BoolExpr encodeConstant_Constant(ConstantSlot lhs, ConstantSlot rhs,
            VariableSlot result) {
        // TODO Auto-generated method stub
        return null;
    }
}
