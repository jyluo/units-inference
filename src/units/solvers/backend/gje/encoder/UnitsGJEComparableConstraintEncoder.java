package units.solvers.backend.gje.encoder;

import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.solvers.backend.gje.UnitsGJEFormatTranslator;
import units.solvers.backend.gje.representation.GJEEquationSet;

public class UnitsGJEComparableConstraintEncoder extends UnitsGJEAbstractConstraintEncoder
        implements ComparableConstraintEncoder<GJEEquationSet> {

    public UnitsGJEComparableConstraintEncoder(
            Lattice lattice, UnitsGJEFormatTranslator formatTranslator) {
        super(lattice, formatTranslator);
    }

    protected GJEEquationSet encode(Slot fst, Slot snd) {
        // fst <: snd or snd <: fst
        // for GJE, this is fst == snd || snd == fst which simplifies to 1
        // equality constraint
        return UnitsGJEEncoderUtils.equality(
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
