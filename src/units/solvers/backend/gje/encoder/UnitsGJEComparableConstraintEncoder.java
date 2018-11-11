package units.solvers.backend.gje.encoder;

import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.solvers.backend.gje.UnitsGJEFormatTranslator;
import units.solvers.backend.gje.representation.GJEEquationSet;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

public class UnitsGJEComparableConstraintEncoder extends UnitsGJEAbstractConstraintEncoder
        implements ComparableConstraintEncoder<GJEEquationSet> {

    public UnitsGJEComparableConstraintEncoder(
            Lattice lattice, UnitsGJEFormatTranslator formatTranslator) {
        super(lattice, formatTranslator);
    }

    // Comparable constraints generated for comparisons??
    protected GJEEquationSet encode(Slot fst, Slot snd) {
        GJEInferenceUnit first = fst.serialize(formatTranslator);
        GJEInferenceUnit second = snd.serialize(formatTranslator);

        return null;
        //        // fst <: snd or snd <: fst
        //        return ctx.mkOr(
        //                UnitsGJEEncoderUtils.subtype(first, second),
        //                UnitsGJEEncoderUtils.subtype(second, first));
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
