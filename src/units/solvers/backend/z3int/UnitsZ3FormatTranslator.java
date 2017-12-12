package units.solvers.backend.z3int;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.AnnotationValue;
import javax.lang.model.element.ExecutableElement;
import org.checkerframework.javacutil.ErrorReporter;
import org.checkerframework.javacutil.Pair;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Model;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Attribute.Compound;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ConstraintEncoderFactory;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;
import units.solvers.backend.z3int.encoder.UnitsZ3EncodedSlot;
import units.solvers.backend.z3int.encoder.UnitsZ3IntConstraintEncoderFactory;
import units.util.UnitsUtils;

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

        UnitsZ3EncodedSlot encodedSlot = UnitsZ3EncodedSlot.makeVariableSlot(ctx, slotID);

        serializedSlots.put(slotID, encodedSlot);
        return encodedSlot;
    }

    @SuppressWarnings("unchecked")
    @Override
    protected UnitsZ3EncodedSlot serializeConstantSlot(ConstantSlot slot) {
        int slotID = slot.getId();

        if (serializedSlots.containsKey(slotID)) {
            return serializedSlots.get(slotID);
        }

        // Makes a constant encoded slot with default values
        UnitsZ3EncodedSlot encodedSlot = UnitsZ3EncodedSlot.makeConstantSlot(ctx, slotID);

        // Replace values in constant encoded slot with values in the constant slot's annotation
        Map<? extends ExecutableElement, ? extends AnnotationValue> elementValues =
                slot.getValue().getElementValues();
        for (ExecutableElement elem : elementValues.keySet()) {

            Object annotationValue = elementValues.get(elem).getValue();

            if (elem.getSimpleName().contentEquals("unknownUnits")) {
                encodedSlot.setUnknownUnits(((Boolean) annotationValue));

            } else if (elem.getSimpleName().contentEquals("unitsBottom")) {
                encodedSlot.setUnitsBottom(((Boolean) annotationValue));

            } else if (elem.getSimpleName().contentEquals("prefixExponent")) {
                encodedSlot.setPrefixExponent(((Integer) annotationValue));

            } else if (elem.getSimpleName().contentEquals("baseUnits")) {
                // for each base unit that is declared
                for (Compound bu : (List<Compound>) annotationValue) {

                    // extract the unit and exponent
                    Map<MethodSymbol, Attribute> buElementValues = bu.getElementValues();
                    String unit = "none";
                    int exponent = 0;

                    for (MethodSymbol key : buElementValues.keySet()) {
                        System.out.println(key.getSimpleName() + " => " + buElementValues.get(key));

                        // TODO: is there any better ways to do this aside from name equality?
                        if (key.getSimpleName().contentEquals("unit")) {
                            unit = buElementValues.get(key).getValue().toString();
                        } else if (key.getSimpleName().contentEquals("exponent")) {
                            exponent =
                                    Integer.valueOf(buElementValues.get(key).getValue().toString());
                        }
                    }

                    encodedSlot.setExponent(unit, exponent);
                }
            }
        }

        serializedSlots.put(slotID, encodedSlot);
        return encodedSlot;
    }

    // Decode overall solutions from Z3
    @Override
    public Map<Integer, AnnotationMirror> decodeSolution(Model model,
            ProcessingEnvironment processingEnv) {

        Map<Integer, AnnotationMirror> result = new HashMap<>();
        Map<Integer, UnitsZ3EncodedSlot> solutionSlots = new HashMap<>();

        System.out.println("========== SOLUTION ==========");

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
                    UnitsUtils.slotFromZ3VarName(funcDecl.getName().toString());
            int slotID = slot.first;
            String component = slot.second;

            // Create a fresh constant encoded slot if needed in the map
            if (!solutionSlots.containsKey(slotID)) {
                solutionSlots.put(slotID, UnitsZ3EncodedSlot.makeConstantSlot(ctx, slotID));
            }

            // TODO: could define a SolutionSlot datatype with primitive bools and ints
            UnitsZ3EncodedSlot z3Slot = solutionSlots.get(slotID);
            if (component.contentEquals(UnitsUtils.uuSlotName)) {
                z3Slot.setUnknownUnits(constInterp.isTrue());
            } else if (component.contentEquals(UnitsUtils.ubSlotName)) {
                z3Slot.setUnitsBottom(constInterp.isTrue());
            } else if (component.contentEquals(UnitsUtils.prefixSlotName)) {
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
    public AnnotationMirror decodeSolution(UnitsZ3EncodedSlot solutionSlot,
            ProcessingEnvironment processingEnv) {
        System.out.println(solutionSlot);
        return null;
    }

}
