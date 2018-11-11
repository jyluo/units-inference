package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.representation.TypecheckUnit;
import units.solvers.backend.gje.representation.GJEEquationSet;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

public class UnitsGJEEqualityConstraintEncoder
        extends GJEAbstractConstraintEncoder<GJEInferenceUnit, TypecheckUnit>
        implements EqualityConstraintEncoder<GJEEquationSet> {

    public UnitsGJEEqualityConstraintEncoder(
            Lattice lattice,
            GJEFormatTranslator<GJEInferenceUnit, TypecheckUnit> gjeFormatTranslator) {
        super(lattice, gjeFormatTranslator);
    }

    // 2 Slots are equal if their components are equal
    protected GJEEquationSet encode(Slot fst, Slot snd) {
        return null;
        //        return UnitsGJEEncoderUtils.equality(fst.serialize(gjeFormatTranslator),
        //                snd.serialize(gjeFormatTranslator));
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
