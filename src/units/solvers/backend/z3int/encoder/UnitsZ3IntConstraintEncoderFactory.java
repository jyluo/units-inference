package units.solvers.backend.z3int.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.backend.encoder.binary.InequalityConstraintEncoder;
import checkers.inference.solver.backend.encoder.combine.CombineConstraintEncoder;
import checkers.inference.solver.backend.encoder.existential.ExistentialConstraintEncoder;
import checkers.inference.solver.backend.encoder.preference.PreferenceConstraintEncoder;
import checkers.inference.solver.backend.encoder.ternary.AdditionConstraintEncoder;
import checkers.inference.solver.backend.encoder.ternary.DivisionConstraintEncoder;
import checkers.inference.solver.backend.encoder.ternary.ModulusConstraintEncoder;
import checkers.inference.solver.backend.encoder.ternary.MultiplicationConstraintEncoder;
import checkers.inference.solver.backend.encoder.ternary.SubtractionConstraintEncoder;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.backend.z3Int.encoder.Z3IntConstraintEncoderFactory;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;

/**
 * Z3 implementation of {@link checkers.inference.solver.backend.encoder.ConstraintEncoderFactory}
 * for Units Type System.
 *
 * @see checkers.inference.solver.backend.encoder.ConstraintEncoderFactory
 */
public class UnitsZ3IntConstraintEncoderFactory
        extends Z3IntConstraintEncoderFactory<UnitsZ3EncodedSlot, UnitsZ3EncodedSlot> {
    public UnitsZ3IntConstraintEncoderFactory(Lattice lattice, ConstraintVerifier verifier,
            Context ctx,
            Z3IntFormatTranslator<UnitsZ3EncodedSlot, UnitsZ3EncodedSlot> z3IntFormatTranslator) {
        super(lattice, verifier, ctx, z3IntFormatTranslator);
    }

    @Override
    public UnitsZ3IntSubtypeConstraintEncoder createSubtypeConstraintEncoder() {
        return new UnitsZ3IntSubtypeConstraintEncoder(
                lattice, verifier, ctx, z3IntFormatTranslator);
    }

    @Override
    public EqualityConstraintEncoder<BoolExpr> createEqualityConstraintEncoder() {
        return new UnitsZ3IntEqualityConstraintEncoder(
                lattice, verifier, ctx, z3IntFormatTranslator);
    }

    @Override
    public InequalityConstraintEncoder<BoolExpr> createInequalityConstraintEncoder() {
        return null;
    }

    @Override
    public ComparableConstraintEncoder<BoolExpr> createComparableConstraintEncoder() {
        return null;
    }

    @Override
    public PreferenceConstraintEncoder<BoolExpr> createPreferenceConstraintEncoder() {
        return null;
    }

    @Override
    public ExistentialConstraintEncoder<BoolExpr> createExistentialConstraintEncoder() {
        return null;
    }

    @Override
    public CombineConstraintEncoder<BoolExpr> createCombineConstraintEncoder() {
        return null;
    }

    @Override
    public AdditionConstraintEncoder<BoolExpr> createAdditionConstraintEncoder() {
        return new UnitsZ3IntAdditionConstraintEncoder(
                lattice, verifier, ctx, z3IntFormatTranslator);
    }

    @Override
    public SubtractionConstraintEncoder<BoolExpr> createSubtractionConstraintEncoder() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public MultiplicationConstraintEncoder<BoolExpr> createMultiplicationConstraintEncoder() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public DivisionConstraintEncoder<BoolExpr> createDivisionConstraintEncoder() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ModulusConstraintEncoder<BoolExpr> createModulusConstraintEncoder() {
        // TODO Auto-generated method stub
        return null;
    }
}
