package units.solvers.backend.z3smt.encoder;

import backend.z3smt.encoder.Z3SmtConstraintEncoderFactory;
import checkers.inference.solver.backend.encoder.ArithmeticConstraintEncoder;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.backend.encoder.binary.InequalityConstraintEncoder;
import checkers.inference.solver.backend.encoder.combine.CombineConstraintEncoder;
import checkers.inference.solver.backend.encoder.existential.ExistentialConstraintEncoder;
import checkers.inference.solver.backend.encoder.implication.ImplicationConstraintEncoder;
import checkers.inference.solver.backend.encoder.preference.PreferenceConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import units.solvers.backend.z3smt.UnitsZ3SmtFormatTranslator;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;
import units.utils.TypecheckUnit;

/**
 * Z3 implementation of {@link checkers.inference.solver.backend.encoder.ConstraintEncoderFactory}
 * for Units Type System.
 *
 * @see checkers.inference.solver.backend.encoder.ConstraintEncoderFactory
 */
public class UnitsZ3SmtConstraintEncoderFactory
        extends Z3SmtConstraintEncoderFactory<
                Z3InferenceUnit, TypecheckUnit, UnitsZ3SmtFormatTranslator> {
    public UnitsZ3SmtConstraintEncoderFactory(
            Lattice lattice, Context ctx, UnitsZ3SmtFormatTranslator z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    @Override
    public UnitsZ3SmtSubtypeConstraintEncoder createSubtypeConstraintEncoder() {
        return new UnitsZ3SmtSubtypeConstraintEncoder(lattice, ctx, formatTranslator);
    }

    @Override
    public EqualityConstraintEncoder<BoolExpr> createEqualityConstraintEncoder() {
        return new UnitsZ3SmtEqualityConstraintEncoder(lattice, ctx, formatTranslator);
    }

    @Override
    public InequalityConstraintEncoder<BoolExpr> createInequalityConstraintEncoder() {
        return null;
    }

    @Override
    public ComparableConstraintEncoder<BoolExpr> createComparableConstraintEncoder() {
        return new UnitsZ3SmtComparableConstraintEncoder(lattice, ctx, formatTranslator);
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
    public ImplicationConstraintEncoder<BoolExpr> createImplicationConstraintEncoder() {
        return null;
    }

    @Override
    public ArithmeticConstraintEncoder<BoolExpr> createArithmeticConstraintEncoder() {
        return new UnitsZ3SmtArithmeticConstraintEncoder(lattice, ctx, formatTranslator);
    }
}
