package units.solvers.backend.gje;

import backend.gje.GJEFormatTranslator;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ConstraintEncoderFactory;
import checkers.inference.solver.frontend.Lattice;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import units.representation.TypecheckUnit;
import units.representation.UnitsRepresentationUtils;
import units.solvers.backend.gje.encoder.UnitsGJEConstraintEncoderFactory;
import units.solvers.backend.gje.representation.GJEEquationSet;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

public class UnitsGJEFormatTranslator extends GJEFormatTranslator<GJEInferenceUnit, TypecheckUnit> {

    // static reference to the singleton instance
    protected static UnitsRepresentationUtils unitsRepUtils;

    public UnitsGJEFormatTranslator(Lattice lattice) {
        super(lattice);
        unitsRepUtils = UnitsRepresentationUtils.getInstance();
    }

    @Override
    protected ConstraintEncoderFactory<GJEEquationSet> createConstraintEncoderFactory() {
        return new UnitsGJEConstraintEncoderFactory(lattice, this);
    }

    @Override
    protected GJEInferenceUnit serializeVarSlot(VariableSlot slot) {
        int cfiSlotID = slot.getId();
        int gjeSlotID = slotCFItoGJEMap.get(slot);

        if (serializedSlots.containsKey(cfiSlotID)) {
            return serializedSlots.get(cfiSlotID);
        }

        GJEInferenceUnit encodedSlot = GJEInferenceUnit.makeVariableSlot(cfiSlotID, gjeSlotID);

        serializedSlots.put(cfiSlotID, encodedSlot);
        return encodedSlot;
    }

    @Override
    protected GJEInferenceUnit serializeConstantSlot(ConstantSlot slot) {
        int slotID = slot.getId();

        if (serializedSlots.containsKey(slotID)) {
            return serializedSlots.get(slotID);
        }

        AnnotationMirror anno = slot.getValue();

        // Temp Hack: forcefully encode constant slot for poly qualifiers as
        // unknownunits
        if (AnnotationUtils.areSame(anno, unitsRepUtils.POLYUNIT)
                || AnnotationUtils.areSame(anno, unitsRepUtils.POLYALL)) {
            anno = unitsRepUtils.TOP;
        }

        // if for some reason a raw internal appears, then treat it as
        // dimensionless
        if (AnnotationUtils.areSame(anno, unitsRepUtils.RAWUNITSINTERNAL)) {
            // TODO: maybe raise error?
            anno = unitsRepUtils.DIMENSIONLESS;
        }

        // System.out.println(" ==== creating constant slot for " + anno);

        TypecheckUnit unit = unitsRepUtils.createTypecheckUnit(anno);

        // Makes a constant encoded slot with default values
        GJEInferenceUnit encodedSlot = GJEInferenceUnit.makeConstantSlot(slotID);

        // Replace values in constant encoded slot with values in the annotation
        if (unit.isUnknownUnits()) {
            encodedSlot.setUnknownUnits(true);
        } else if (unit.isUnitsBottom()) {
            encodedSlot.setUnitsBottom(true);
        } else {
            encodedSlot.setPrefixExponent(unit.getPrefixExponent());
            Map<String, Integer> expos = unit.getExponents();
            for (String bu : expos.keySet()) {
                encodedSlot.setExponent(bu, unit.getExponent(bu));
            }
        }

        serializedSlots.put(slotID, encodedSlot);
        return encodedSlot;
    }

    // Decode overall solutions from Z3
    @Override
    public Map<Integer, AnnotationMirror> decodeSolution(
            List<String> model, ProcessingEnvironment processingEnv) {

        Map<Integer, AnnotationMirror> result = new HashMap<>();
        // Map<Integer, TypecheckUnit> solutionSlots = new HashMap<>();
        //
        // for (String line : model) {
        // // each line is "varName value"
        // String[] parts = line.split(" ");
        // String varName = parts[0];
        // String value = parts[1];
        //
        // // Get slotID and component name
        // Pair<Integer, String> slot =
        // UnitsGJEEncoderUtils.slotFromZ3VarName(varName);
        // int slotID = slot.first;
        // String component = slot.second;
        //
        // // Create a fresh solution slot if needed in the map
        // if (!solutionSlots.containsKey(slotID)) {
        // solutionSlots.put(slotID, new TypecheckUnit());
        // }
        //
        // TypecheckUnit z3Slot = solutionSlots.get(slotID);
        // if (component.contentEquals(UnitsGJEEncoderUtils.uuSlotName)) {
        // z3Slot.setUnknownUnits(Boolean.parseBoolean(value));
        // } else if (component.contentEquals(UnitsGJEEncoderUtils.ubSlotName))
        // {
        // z3Slot.setUnitsBottom(Boolean.parseBoolean(value));
        // } else if
        // (component.contentEquals(UnitsGJEEncoderUtils.prefixSlotName)) {
        // z3Slot.setPrefixExponent(Integer.parseInt(value));
        // } else {
        // // assumes it is a base unit exponent
        // z3Slot.setExponent(component, Integer.parseInt(value));
        // }
        //
        // // DEBUG:
        // // System.out.println(" " + varName + " => " + value);
        // // 10-s => -3
        // // 10-m => 1
        // // 10-Prefix => 0
        // // 10-UnitsBottom => false
        // // 10-UnknownUnits => true
        // // 10 : UU = true UB = false p = 0 m = 1 s = -3
        // }
        //
        // for (Integer slotID : solutionSlots.keySet()) {
        // result.put(slotID, decodeSolution(solutionSlots.get(slotID),
        // processingEnv));
        // }

        return result;
    }

    // Convert a UnitsZ3EncodedSlot to an AnnotationMirror
    @Override
    public AnnotationMirror decodeSolution(
            TypecheckUnit solutionSlot, ProcessingEnvironment processingEnv) {

        // TODO: translate @UnitsInternal annotations to string from @Units
        // annotations
        // TODO: infer original name somehow

        AnnotationMirror solutionUnit =
                unitsRepUtils.createInternalUnit(
                        "",
                        solutionSlot.isUnknownUnits(),
                        solutionSlot.isUnitsBottom(),
                        solutionSlot.getPrefixExponent(),
                        solutionSlot.getExponents());

        // Always return top and bottom based on the booleans, since the BU
        // values can be arbitrary
        if (solutionSlot.isUnknownUnits()) {
            return unitsRepUtils.SURFACE_TOP;
        } else if (solutionSlot.isUnitsBottom()) {
            return unitsRepUtils.SURFACE_BOTTOM;
        } else {
            return unitsRepUtils.getSurfaceUnit(solutionUnit);
        }
    }
}
