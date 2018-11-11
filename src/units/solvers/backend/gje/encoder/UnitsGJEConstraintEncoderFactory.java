package units.solvers.backend.gje.encoder;

import checkers.inference.solver.backend.encoder.AbstractConstraintEncoderFactory;
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
import units.solvers.backend.gje.UnitsGJEFormatTranslator;
import units.solvers.backend.gje.representation.GJEEquationSet;

/**
 * GJE implementation of {@link checkers.inference.solver.backend.encoder.ConstraintEncoderFactory}
 * for Units Type System.
 *
 * @see checkers.inference.solver.backend.encoder.ConstraintEncoderFactory
 */
public class UnitsGJEConstraintEncoderFactory
        extends AbstractConstraintEncoderFactory<GJEEquationSet, UnitsGJEFormatTranslator> {

    public UnitsGJEConstraintEncoderFactory(
            Lattice lattice, UnitsGJEFormatTranslator formatTranslator) {
        super(lattice, formatTranslator);
    }

    @Override
    public SubtypeConstraintEncoder<GJEEquationSet> createSubtypeConstraintEncoder() {
        return new UnitsGJESubtypeConstraintEncoder(lattice, formatTranslator);
    }

    @Override
    public EqualityConstraintEncoder<GJEEquationSet> createEqualityConstraintEncoder() {
        return new UnitsGJEEqualityConstraintEncoder(lattice, formatTranslator);
    }

    @Override
    public InequalityConstraintEncoder<GJEEquationSet> createInequalityConstraintEncoder() {
        return null;
    }

    @Override
    public ComparableConstraintEncoder<GJEEquationSet> createComparableConstraintEncoder() {
        return new UnitsGJEComparableConstraintEncoder(lattice, formatTranslator);
    }

    @Override
    public PreferenceConstraintEncoder<GJEEquationSet> createPreferenceConstraintEncoder() {
        return null;
    }

    @Override
    public ExistentialConstraintEncoder<GJEEquationSet> createExistentialConstraintEncoder() {
        return null;
    }

    @Override
    public CombineConstraintEncoder<GJEEquationSet> createCombineConstraintEncoder() {
        return null;
    }

    @Override
    public ImplicationConstraintEncoder<GJEEquationSet> createImplicationConstraintEncoder() {
        return null;
    }

    @Override
    public ArithmeticConstraintEncoder<GJEEquationSet> createArithmeticConstraintEncoder() {
        return new UnitsGJEArithmeticConstraintEncoder(lattice, formatTranslator);
    }
}
