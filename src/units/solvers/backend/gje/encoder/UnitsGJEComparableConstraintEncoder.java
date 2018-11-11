package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.ComparableConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.representation.TypecheckUnit;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

public class UnitsGJEComparableConstraintEncoder
        extends GJEAbstractConstraintEncoder<GJEInferenceUnit, TypecheckUnit>
        implements ComparableConstraintEncoder<String> {

    public UnitsGJEComparableConstraintEncoder(
            Lattice lattice,
            GJEFormatTranslator<GJEInferenceUnit, TypecheckUnit> z3SmtFormatTranslator) {
        super(lattice, z3SmtFormatTranslator);
    }

    protected String encode(Slot fst, Slot snd) {
        GJEInferenceUnit first = fst.serialize(gjeFormatTranslator);
        GJEInferenceUnit second = snd.serialize(gjeFormatTranslator);

        return null;
        //        // fst <: snd or snd <: fst
        //        return ctx.mkOr(
        //                UnitsGJEEncoderUtils.subtype(first, second),
        //                UnitsGJEEncoderUtils.subtype(second, first));
    }

    @Override
    public String encodeVariable_Variable(VariableSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public String encodeVariable_Constant(VariableSlot fst, ConstantSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public String encodeConstant_Variable(ConstantSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }
}
