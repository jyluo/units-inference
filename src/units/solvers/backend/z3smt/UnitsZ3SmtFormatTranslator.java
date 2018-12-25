package units.solvers.backend.z3smt;

import backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ConstraintEncoderFactory;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import java.lang.annotation.Annotation;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.Pair;
import units.representation.TypecheckUnit;
import units.representation.UnitsRepresentationUtils;
import units.solvers.backend.z3smt.encoder.UnitsZ3SmtConstraintEncoderFactory;
import units.solvers.backend.z3smt.encoder.UnitsZ3SmtEncoderUtils;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsZ3SmtFormatTranslator
        extends Z3SmtFormatTranslator<Z3InferenceUnit, TypecheckUnit> {

    public static BoolExpr Z3TRUE;
    public static BoolExpr Z3FALSE;

    // static reference to the singleton instance
    protected static UnitsRepresentationUtils unitsRepUtils;

    public UnitsZ3SmtFormatTranslator(Lattice lattice) {
        super(lattice);
        unitsRepUtils = UnitsRepresentationUtils.getInstance();
    }

    @Override
    protected void finishInitializingEncoders() {
        super.finishInitializingEncoders();
        // Context is now available
        UnitsZ3SmtFormatTranslator.Z3TRUE = ctx.mkBool(true);
        UnitsZ3SmtFormatTranslator.Z3FALSE = ctx.mkBool(false);
    }

    @Override
    protected ConstraintEncoderFactory<BoolExpr> createConstraintEncoderFactory() {
        return new UnitsZ3SmtConstraintEncoderFactory(lattice, ctx, this);
    }

    @Override
    protected Z3InferenceUnit serializeVarSlot(VariableSlot slot) {
        int slotID = slot.getId();

        if (serializedSlots.containsKey(slotID)) {
            return serializedSlots.get(slotID);
        }

        Z3InferenceUnit encodedSlot = Z3InferenceUnit.makeVariableSlot(ctx, slotID);

        serializedSlots.put(slotID, encodedSlot);
        return encodedSlot;
    }

    @Override
    protected Z3InferenceUnit serializeConstantSlot(ConstantSlot slot) {
        int slotID = slot.getId();

        if (serializedSlots.containsKey(slotID)) {
            return serializedSlots.get(slotID);
        }

        AnnotationMirror anno = slot.getValue();

        // Temp Hack: forcefully encode constant slot for poly qualifiers as unknownunits
        if (AnnotationUtils.areSame(anno, unitsRepUtils.POLYUNIT)
                || AnnotationUtils.areSame(anno, unitsRepUtils.POLYALL)) {
            anno = unitsRepUtils.TOP;
        }

        // if for some reason a raw internal appears, then treat it as dimensionless
        if (AnnotationUtils.areSame(anno, unitsRepUtils.RAWUNITSINTERNAL)) {
            // TODO: maybe raise error?
            anno = unitsRepUtils.DIMENSIONLESS;
        }

        // System.err.println(" ==== creating constant slot for " + anno);

        TypecheckUnit unit = unitsRepUtils.createTypecheckUnit(anno);

        // Makes a constant encoded slot with default values
        Z3InferenceUnit encodedSlot = Z3InferenceUnit.makeConstantSlot(ctx, slotID);

        // Replace values in constant encoded slot with values in the annotation
        if (unit.isUnknownUnits()) {
            encodedSlot.setUnknownUnits(true);
        } else if (unit.isUnitsBottom()) {
            encodedSlot.setUnitsBottom(true);
        } else {
            encodedSlot.setPrefixExponent(unit.getPrefixExponent());
            Map<Class<? extends Annotation>, Integer> expos = unit.getExponents();
            for (Class<? extends Annotation> bu : expos.keySet()) {
                encodedSlot.setExponent(bu, unit.getExponent(bu));
            }
        }

        serializedSlots.put(slotID, encodedSlot);
        return encodedSlot;
    }

    @Override
    public BoolExpr encodeSlotWellformnessConstraint(VariableSlot slot) {
        if (slot instanceof ConstantSlot) {
            ConstantSlot cs = (ConstantSlot) slot;
            AnnotationMirror anno = cs.getValue();
            // encode PolyAll and PolyUnit as constant trues
            if (AnnotationUtils.areSame(anno, unitsRepUtils.POLYALL)
                    || AnnotationUtils.areSame(anno, unitsRepUtils.POLYUNIT)) {
                return ctx.mkTrue();
            }
        }

        Z3InferenceUnit serializedSlot = slot.serialize(this);
        return UnitsZ3SmtEncoderUtils.slotWellformedness(ctx, serializedSlot);
    }

    @Override
    public BoolExpr encodeSlotPreferenceConstraint(VariableSlot slot) {
        if (slot instanceof ConstantSlot) {
            ConstantSlot cs = (ConstantSlot) slot;
            AnnotationMirror anno = cs.getValue();
            // encode PolyAll and PolyUnit as constant trues
            if (AnnotationUtils.areSame(anno, unitsRepUtils.POLYALL)
                    || AnnotationUtils.areSame(anno, unitsRepUtils.POLYUNIT)) {
                return ctx.mkTrue();
            }
        }

        Z3InferenceUnit serializedSlot = slot.serialize(this);
        return UnitsZ3SmtEncoderUtils.slotPreference(ctx, serializedSlot);
    }

    // Decode overall solutions from Z3
    @Override
    public Map<Integer, AnnotationMirror> decodeSolution(
            List<String> model, ProcessingEnvironment processingEnv) {

        Map<Integer, AnnotationMirror> result = new HashMap<>();
        Map<Integer, TypecheckUnit> solutionSlots = new HashMap<>();

        for (String line : model) {
            // each line is "varName value"
            String[] parts = line.split(" ");
            String varName = parts[0];
            String value = parts[1];

            // Get slotID and component name
            Pair<Integer, String> slot = UnitsZ3SmtEncoderUtils.slotFromZ3VarName(varName);
            int slotID = slot.first;
            String component = slot.second;

            // Create a fresh solution slot if needed in the map
            if (!solutionSlots.containsKey(slotID)) {
                solutionSlots.put(slotID, new TypecheckUnit());
            }

            TypecheckUnit z3Slot = solutionSlots.get(slotID);
            if (component.contentEquals(UnitsZ3SmtEncoderUtils.uuSlotName)) {
                z3Slot.setUnknownUnits(Boolean.parseBoolean(value));
            } else if (component.contentEquals(UnitsZ3SmtEncoderUtils.ubSlotName)) {
                z3Slot.setUnitsBottom(Boolean.parseBoolean(value));
            } else if (component.contentEquals(UnitsZ3SmtEncoderUtils.prefixSlotName)) {
                z3Slot.setPrefixExponent(Integer.parseInt(value));
            } else {
                // assumes it is a base unit exponent
                z3Slot.setExponent(
                        unitsRepUtils.getBaseUnitClass(component), Integer.parseInt(value));
            }

            // DEBUG:
            // System.err.println(" " + varName + " => " + value);
            // 10-s => -3
            // 10-m => 1
            // 10-Prefix => 0
            // 10-UnitsBottom => false
            // 10-UnknownUnits => true
            // 10 : UU = true UB = false p = 0 m = 1 s = -3
        }

        for (Integer slotID : solutionSlots.keySet()) {
            result.put(slotID, decodeSolution(solutionSlots.get(slotID), processingEnv));
        }

        return result;
    }

    // Convert a UnitsZ3EncodedSlot to an AnnotationMirror
    @Override
    public AnnotationMirror decodeSolution(
            TypecheckUnit solutionSlot, ProcessingEnvironment processingEnv) {

        // TODO: translate @UnitsInternal annotations to string from @Units annotations
        // TODO: infer original name somehow

        AnnotationMirror solutionUnit =
                unitsRepUtils.createInternalUnit(
                        "",
                        solutionSlot.isUnknownUnits(),
                        solutionSlot.isUnitsBottom(),
                        solutionSlot.getPrefixExponent(),
                        solutionSlot.getExponents());

        // Always return top and bottom based on the booleans, since the BU values can be arbitrary
        if (solutionSlot.isUnknownUnits()) {
            return unitsRepUtils.SURFACE_TOP;
        } else if (solutionSlot.isUnitsBottom()) {
            return unitsRepUtils.SURFACE_BOTTOM;
        } else {
            return unitsRepUtils.getSurfaceUnit(solutionUnit);
        }
    }
}
