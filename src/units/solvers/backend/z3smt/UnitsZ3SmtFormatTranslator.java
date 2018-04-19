package units.solvers.backend.z3smt;

import java.util.HashMap;
import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ErrorReporter;
import org.checkerframework.javacutil.Pair;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Model;
import backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ConstraintEncoderFactory;
import checkers.inference.solver.frontend.Lattice;
import units.representation.InferenceUnit;
import units.representation.TypecheckUnit;
import units.representation.UnitsRepresentationUtils;
import units.solvers.backend.z3smt.encoder.UnitsZ3SmtConstraintEncoderFactory;
import units.util.UnitsZ3SmtEncoderUtils;

public class UnitsZ3SmtFormatTranslator
        extends Z3SmtFormatTranslator<InferenceUnit, TypecheckUnit> {

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
    protected InferenceUnit serializeVarSlot(VariableSlot slot) {
        int slotID = slot.getId();

        if (serializedSlots.containsKey(slotID)) {
            return serializedSlots.get(slotID);
        }

        InferenceUnit encodedSlot = InferenceUnit.makeVariableSlot(ctx, slotID);

        serializedSlots.put(slotID, encodedSlot);
        return encodedSlot;
    }

    @Override
    protected InferenceUnit serializeConstantSlot(ConstantSlot slot) {
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

        // System.out.println(" ==== creating constant slot for " + anno);

        TypecheckUnit unit = unitsRepUtils.createTypecheckUnit(anno);

        // Makes a constant encoded slot with default values
        InferenceUnit encodedSlot = InferenceUnit.makeConstantSlot(ctx, slotID);

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

        InferenceUnit serializedSlot = slot.serialize(this);
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

        InferenceUnit serializedSlot = slot.serialize(this);
        return UnitsZ3SmtEncoderUtils.slotPreference(ctx, serializedSlot);
    }

    // Decode overall solutions from Z3
    @Override
    public Map<Integer, AnnotationMirror> decodeSolution(Model model,
            ProcessingEnvironment processingEnv) {

        Map<Integer, AnnotationMirror> result = new HashMap<>();
        Map<Integer, TypecheckUnit> solutionSlots = new HashMap<>();

        // Model maps slotID-component to IntNum or BoolExpr
        // We collect all components for a given slotID, creating a solution slot for each slotID
        // and filling it in.
        // Each funcDecl is a z3 variable (internally declared as a z3 function with name =
        // slotID-component, and value = results of inference)
        // eg: (declare-fun 10-m () Int) := 21 // meter of varAnnot(10) has a solution of 21
        for (FuncDecl funcDecl : model.getDecls()) {
            // Get the result value from inference
            Expr constInterp = model.getConstInterp(funcDecl);

            if (!(constInterp instanceof IntNum || constInterp instanceof BoolExpr)) {
                ErrorReporter.errorAbort(
                        "Wrong solution type detected for z3Var " + funcDecl.getName().toString()
                                + ": All solution must be type of IntNum or BoolExpr, but got "
                                + constInterp.getClass() + " instead.");
            }

            // Get slotID and component name
            Pair<Integer, String> slot =
                    UnitsZ3SmtEncoderUtils.slotFromZ3VarName(funcDecl.getName().toString());
            int slotID = slot.first;
            String component = slot.second;

            // Create a fresh solution slot if needed in the map
            if (!solutionSlots.containsKey(slotID)) {
                solutionSlots.put(slotID, new TypecheckUnit());
            }

            TypecheckUnit z3Slot = solutionSlots.get(slotID);
            if (component.contentEquals(UnitsZ3SmtEncoderUtils.uuSlotName)) {
                z3Slot.setUnknownUnits(constInterp.isTrue());
            } else if (component.contentEquals(UnitsZ3SmtEncoderUtils.ubSlotName)) {
                z3Slot.setUnitsBottom(constInterp.isTrue());
            } else if (component.contentEquals(UnitsZ3SmtEncoderUtils.prefixSlotName)) {
                z3Slot.setPrefixExponent(Integer.valueOf(constInterp.toString()));
            } else {
                // assumes it is a base unit exponent
                z3Slot.setExponent(component, Integer.valueOf(constInterp.toString()));
            }

            // DEBUG:
            // System.out.println(" " + funcDecl.getName().toString() + " => " + constInterp);
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
    public AnnotationMirror decodeSolution(TypecheckUnit solutionSlot,
            ProcessingEnvironment processingEnv) {

        // TODO: translate @UnitsInternal annotations to string from @Units annotations
        // TODO: infer original name somehow

        AnnotationMirror solutionUnit = unitsRepUtils.createInternalUnit("",
                solutionSlot.isUnknownUnits(), solutionSlot.isUnitsBottom(),
                solutionSlot.getPrefixExponent(), solutionSlot.getExponents());

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
