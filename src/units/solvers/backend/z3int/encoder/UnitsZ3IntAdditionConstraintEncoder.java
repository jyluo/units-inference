package units.solvers.backend.z3int.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ternary.AdditionConstraintEncoder;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.encoder.Z3IntAbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;

public class UnitsZ3IntAdditionConstraintEncoder extends Z3IntAbstractConstraintEncoder
        implements AdditionConstraintEncoder<BoolExpr> {

    public UnitsZ3IntAdditionConstraintEncoder(Lattice lattice, ConstraintVerifier verifier,
            Context context, Z3IntFormatTranslator z3IntFormatTranslator) {
        super(lattice, verifier, context, z3IntFormatTranslator);
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
