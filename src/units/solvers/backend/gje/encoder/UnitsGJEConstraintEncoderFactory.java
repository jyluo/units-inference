package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEConstraintEncoderFactory;
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
import java.util.Map;
import java.util.Set;
import units.representation.TypecheckUnit;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

/**
 * GJE implementation of {@link checkers.inference.solver.backend.encoder.ConstraintEncoderFactory}
 * for Units Type System.
 *
 * @see checkers.inference.solver.backend.encoder.ConstraintEncoderFactory
 */
public class UnitsGJEConstraintEncoderFactory
        extends GJEConstraintEncoderFactory<GJEInferenceUnit, TypecheckUnit> {
    public UnitsGJEConstraintEncoderFactory(
            Lattice lattice,
            GJEFormatTranslator<GJEInferenceUnit, TypecheckUnit> gjeFormatTranslator) {
        super(lattice, gjeFormatTranslator);
    }

    @Override
    public SubtypeConstraintEncoder<Map<String, Set<String>>> createSubtypeConstraintEncoder() {
        return new UnitsGJESubtypeConstraintEncoder(lattice, formatTranslator);
    }

    @Override
    public EqualityConstraintEncoder<Map<String, Set<String>>> createEqualityConstraintEncoder() {
        return new UnitsGJEEqualityConstraintEncoder(lattice, formatTranslator);
    }

    @Override
    public InequalityConstraintEncoder<Map<String, Set<String>>>
            createInequalityConstraintEncoder() {
        return null;
    }

    @Override
    public ComparableConstraintEncoder<Map<String, Set<String>>>
            createComparableConstraintEncoder() {
        return new UnitsGJEComparableConstraintEncoder(lattice, formatTranslator);
    }

    @Override
    public PreferenceConstraintEncoder<Map<String, Set<String>>>
            createPreferenceConstraintEncoder() {
        return null;
    }

    @Override
    public ExistentialConstraintEncoder<Map<String, Set<String>>>
            createExistentialConstraintEncoder() {
        return null;
    }

    @Override
    public CombineConstraintEncoder<Map<String, Set<String>>> createCombineConstraintEncoder() {
        return null;
    }

    @Override
    public ImplicationConstraintEncoder<Map<String, Set<String>>>
            createImplicationConstraintEncoder() {
        return null;
    }

    @Override
    public ArithmeticConstraintEncoder<Map<String, Set<String>>>
            createArithmeticConstraintEncoder() {
        return new UnitsGJEArithmeticConstraintEncoder(lattice, formatTranslator);
    }
}
