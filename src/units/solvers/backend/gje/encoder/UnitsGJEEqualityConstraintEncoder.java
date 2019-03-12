package units.solvers.backend.gje.encoder;

import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.solvers.backend.gje.UnitsGJEFormatTranslator;
import units.solvers.backend.gje.representation.GJEEquationSet;

public class UnitsGJEEqualityConstraintEncoder extends UnitsGJEAbstractConstraintEncoder
        implements EqualityConstraintEncoder<GJEEquationSet> {

    public UnitsGJEEqualityConstraintEncoder(
            Lattice lattice, UnitsGJEFormatTranslator formatTranslator) {
        super(lattice, formatTranslator);
    }

    // 2 Slots are equal if their components are equal
    protected GJEEquationSet encode(Slot fst, Slot snd) {
        return unitsGJEEncoderUtils.equality(
                fst.serialize(formatTranslator), snd.serialize(formatTranslator));
    }

    @Override
    public GJEEquationSet encodeVariable_Variable(VariableSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public GJEEquationSet encodeVariable_Constant(VariableSlot fst, ConstantSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public GJEEquationSet encodeConstant_Variable(ConstantSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }
}
