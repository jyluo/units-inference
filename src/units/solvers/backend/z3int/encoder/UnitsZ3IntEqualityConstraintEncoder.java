package units.solvers.backend.z3int.encoder;

import java.util.Set;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.encoder.Z3IntAbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;

public class UnitsZ3IntEqualityConstraintEncoder extends Z3IntAbstractConstraintEncoder
        implements EqualityConstraintEncoder<BoolExpr> {

    public UnitsZ3IntEqualityConstraintEncoder(Lattice lattice, ConstraintVerifier verifier,
            Context context, Z3IntFormatTranslator z3IntFormatTranslator) {
        super(lattice, verifier, context, z3IntFormatTranslator);
    }

    // fornow very hacky
    // fst = snd iff the int value is equal
    protected BoolExpr encode(Slot fst, Slot snd) {
        Set<Expr> varBv1 = fst.serialize(z3IntFormatTranslator);
        Set<Expr> varBv2 = snd.serialize(z3IntFormatTranslator);
        
        // TODO: move this class into Units encoder and specialize
        return null; // context.mkEq(varBv1, varBv2);
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

    @Override
    public BoolExpr encodeConstant_Constant(ConstantSlot fst, ConstantSlot snd) {
        return verifier.areEqual(fst, snd) ? emptyValue : contradictoryValue;
    }
}
