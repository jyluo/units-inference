package units.solvers.backend.z3int;

import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.AnnotationValue;
import javax.lang.model.element.ExecutableElement;
import com.microsoft.z3.BoolExpr;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ConstraintEncoderFactory;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;
import units.solvers.backend.z3int.encoder.UnitsZ3EncodedSlot;
import units.solvers.backend.z3int.encoder.UnitsZ3IntConstraintEncoderFactory;

public class UnitsZ3FormatTranslator
        extends Z3IntFormatTranslator<UnitsZ3EncodedSlot, UnitsZ3EncodedSlot> {

    public static BoolExpr Z3TRUE;
    public static BoolExpr Z3FALSE;

    public UnitsZ3FormatTranslator(Lattice lattice) {
        super(lattice);
    }

    @Override
    protected void finishInitializingEncoders() {
        super.finishInitializingEncoders();
        // Context is now available
        UnitsZ3FormatTranslator.Z3TRUE = ctx.mkBool(true);
        UnitsZ3FormatTranslator.Z3FALSE = ctx.mkBool(false);
    }

    @Override
    protected ConstraintEncoderFactory<BoolExpr> createConstraintEncoderFactory(
            ConstraintVerifier verifier) {
        return new UnitsZ3IntConstraintEncoderFactory(lattice, verifier, ctx, this);
    }

    @Override
    protected UnitsZ3EncodedSlot serializeVarSlot(VariableSlot slot) {
        int slotID = slot.getId();

        if (serializedSlots.containsKey(slotID)) {
            return serializedSlots.get(slotID);
        }

        UnitsZ3EncodedSlot encodedSlot = UnitsZ3EncodedSlot.MakeVariable(ctx, slotID);

        // // var slots have a label = slot ID
        // IntExpr varSlot = context.mkIntConst(String.valueOf(slot.getId()));
        // serializedSlots.put(slotId, varSlot);

        return encodedSlot;
    }

    @Override
    protected UnitsZ3EncodedSlot serializeConstantSlot(ConstantSlot slot) {
        int slotID = slot.getId();

        if (serializedSlots.containsKey(slotID)) {
            return serializedSlots.get(slotID);
        }

        UnitsZ3EncodedSlot encodedSlot = UnitsZ3EncodedSlot.MakeConstant(ctx, slotID);
        AnnotationMirror anno = slot.getValue();

        // // Raw UnitsInternal is the same as Dimensionless
        // if (AnnotationUtils.areSame(anno, UnitsUtils.RAWUNITSINTERNAL)) {
        // BoolExpr bUU = context
        // .mkBoolConst(UnitsUtils.slotName(slotID, UnknownUnits.class.getSimpleName()));
        // context.mkEq(bUU, Z3FALSE);
        //
        // BoolExpr bBT = context
        // .mkBoolConst(UnitsUtils.slotName(slotID, UnitsBottom.class.getSimpleName()));
        // context.mkEq(bBT, Z3FALSE);
        //
        // for (String baseUnit : UnitsUtils.baseUnits()) {
        // IntExpr iBU = context.mkIntConst(UnitsUtils.slotName(slotID, baseUnit));
        // result = context.mkAnd(result, context.mkEq(iBU, context.mkInt(0)));
        // }
        // }

        Map<? extends ExecutableElement, ? extends AnnotationValue> elementValues =
                anno.getElementValues();
        for (ExecutableElement elem : elementValues.keySet()) {
            System.out.println(" == elem ==> " + elementValues.get(elem));
        }

        // // const slots have a value = encoded version of the annotation mirror
        // IntNum constSlot = context.mkInt(z3IntCodec.encodeConstantAM(slot.getValue()));
        // serializedSlots.put(slotId, constSlot);

        return encodedSlot;
    }

    @Override
    public AnnotationMirror decodeSolution(UnitsZ3EncodedSlot solution,
            ProcessingEnvironment processingEnvironment) {
        // TODO Auto-generated method stub
        return null;
    }

    //
    // @Override
    // public BoolExpr serialize(SubtypeConstraint constraint) {
    // // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
    // // POLY_ONTOLOGY into the domain.
    // // TODO: how to encode POLY?
    // for (Slot slot : constraint.getSlots()) {
    // if (isPolyUnit(slot)) {
    // // Return true as empty value, to filter out poly ontology.
    // // TODO: Make encoder.emptyValue public, then using that consistent empty value
    // // here.
    // return context.mkTrue();
    // }
    // }
    //
    // // Soft constraints for subtypeConstraint
    // Slot subtypeSlot = constraint.getSubtype();
    // Slot supertypeSlot = constraint.getSupertype();
    // IntExpr subtypeBV = subtypeSlot.serialize(this);
    // IntExpr supertypeBV = supertypeSlot.serialize(this);
    // // int weight = 1;
    // // if (subtypeSlot instanceof ConstantSlot) {
    // // weight = 2;
    // // }
    //
    // addConstraint(context.mkEq(subtypeBV, supertypeBV));
    // return super.serialize(constraint);
    // }
    //
    // @Override
    // public BoolExpr serialize(EqualityConstraint constraint) {
    // // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
    // // POLY_ONTOLOGY into the domain.
    // // TODO: how to encode POLY?
    // for (Slot slot : constraint.getSlots()) {
    // if (isPolyUnit(slot)) {
    // // Return true as empty value, to filter out poly ontology.
    // // TODO: Make encoder.emptyValue public, then using that consistent empty value
    // // here.
    // return context.mkTrue();
    // }
    // }
    // return super.serialize(constraint);
    // }
    //
    // @Override
    // public BoolExpr serialize(InequalityConstraint constraint) {
    // // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
    // // POLY_ONTOLOGY into the domain.
    // // TODO: how to encode POLY?
    // for (Slot slot : constraint.getSlots()) {
    // if (isPolyUnit(slot)) {
    // // Return true as empty value, to filter out poly ontology.
    // // TODO: Make encoder.emptyValue public, then using that consistent empty value
    // // here.
    // return context.mkTrue();
    // }
    // }
    // return super.serialize(constraint);
    // }
    //
    // protected boolean isPolyUnit(Slot slot) {
    // UnitsUtils.getInstance();
    // return slot instanceof ConstantSlot && AnnotationUtils
    // .areSameIgnoringValues(((ConstantSlot) slot).getValue(), UnitsUtils.POLYUNIT);
    // }
}
