package units.solvers.backend.z3smt.encoder;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.encoder.Z3SmtConstraintEncoderFactory;
import checkers.inference.solver.backend.encoder.ArithmeticConstraintEncoder;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.backend.encoder.binary.InequalityConstraintEncoder;
import checkers.inference.solver.backend.encoder.binary.SubtypeConstraintEncoder;
import checkers.inference.solver.backend.encoder.combine.CombineConstraintEncoder;
import checkers.inference.solver.backend.encoder.existential.ExistentialConstraintEncoder;
import checkers.inference.solver.backend.encoder.implication.ImplicationConstraintEncoder;
import checkers.inference.solver.backend.encoder.preference.PreferenceConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.Context;
import units.representation.TypecheckUnit;
import units.solvers.backend.z3smt.representation.Z3EquationSet;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

/**
 * Z3 implementation of {@link checkers.inference.solver.backend.encoder.ConstraintEncoderFactory}
 * for Units Type System.
 *
 * @see checkers.inference.solver.backend.encoder.ConstraintEncoderFactory
 */
public class UnitsZ3SmtConstraintEncoderFactory
        extends Z3SmtConstraintEncoderFactory<Z3InferenceUnit, Z3EquationSet, TypecheckUnit> {
    public UnitsZ3SmtConstraintEncoderFactory(
            Lattice lattice,
            Context ctx,
            Z3SmtFormatTranslator<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
                    z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    @Override
    public SubtypeConstraintEncoder<Z3EquationSet> createSubtypeConstraintEncoder() {
        return new UnitsZ3SmtSubtypeConstraintEncoder(lattice, ctx, formatTranslator);
    }

    @Override
    public EqualityConstraintEncoder<Z3EquationSet> createEqualityConstraintEncoder() {
        return new UnitsZ3SmtEqualityConstraintEncoder(lattice, ctx, formatTranslator);
    }

    @Override
    public InequalityConstraintEncoder<Z3EquationSet> createInequalityConstraintEncoder() {
        return null;
    }

    @Override
    public ComparableConstraintEncoder<Z3EquationSet> createComparableConstraintEncoder() {
        return new UnitsZ3SmtComparableConstraintEncoder(lattice, ctx, formatTranslator);
    }

    @Override
    public PreferenceConstraintEncoder<Z3EquationSet> createPreferenceConstraintEncoder() {
        return null;
    }

    @Override
    public ExistentialConstraintEncoder<Z3EquationSet> createExistentialConstraintEncoder() {
        return null;
    }

    @Override
    public CombineConstraintEncoder<Z3EquationSet> createCombineConstraintEncoder() {
        return null;
    }

    @Override
    public ImplicationConstraintEncoder<Z3EquationSet> createImplicationConstraintEncoder() {
        return null;
    }

    @Override
    public ArithmeticConstraintEncoder<Z3EquationSet> createArithmeticConstraintEncoder() {
        return new UnitsZ3SmtArithmeticConstraintEncoder(lattice, ctx, formatTranslator);
    }
}
