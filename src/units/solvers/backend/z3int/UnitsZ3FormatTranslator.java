package units.solvers.backend.z3int;

import java.util.HashSet;
import java.util.Set;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ConstraintEncoderFactory;
import checkers.inference.solver.backend.z3Int.Z3IntCodec;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.util.ConstraintVerifier;
import units.solvers.backend.z3int.encoder.UnitsZ3IntConstraintEncoderFactory;

public class UnitsZ3FormatTranslator extends Z3IntFormatTranslator {

    public UnitsZ3FormatTranslator(Lattice lattice) {
        super(lattice);
    }

    @Override
    protected Z3IntCodec createZ3IntCodec() {
        return new UnitsZ3IntCodec();
    }
    
    @Override
    protected ConstraintEncoderFactory<BoolExpr> createConstraintEncoderFactory(
            ConstraintVerifier verifier) {
        return new UnitsZ3IntConstraintEncoderFactory(lattice, verifier, context, this);
    }

    // TODO: for now, each slot maps to a single Z3 int variable, need to upgrade to make a set
    @Override
    protected Set<Expr> serializeVarSlot(VariableSlot slot) {
        int slotId = slot.getId();

        if (serializedSlots.containsKey(slotId)) {
            return serializedSlots.get(slotId);
        }

        Set<Expr> encodedSlot = new HashSet<>();

        // // var slots have a label = slot ID
        // IntExpr varSlot = context.mkIntConst(String.valueOf(slot.getId()));
        // serializedSlots.put(slotId, varSlot);

        return encodedSlot;
    }

    @Override
    protected Set<Expr> serializeConstantSlot(ConstantSlot slot) {
        int slotId = slot.getId();

        if (serializedSlots.containsKey(slotId)) {
            return serializedSlots.get(slotId);
        }

        Set<Expr> encodedSlot = new HashSet<>();

        // // const slots have a value = encoded version of the annotation mirror
        // IntNum constSlot = context.mkInt(z3IntCodec.encodeConstantAM(slot.getValue()));
        // serializedSlots.put(slotId, constSlot);

        return encodedSlot;
    }
    
//
//    @Override
//    public BoolExpr serialize(SubtypeConstraint constraint) {
//        // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
//        // POLY_ONTOLOGY into the domain.
//        // TODO: how to encode POLY?
//        for (Slot slot : constraint.getSlots()) {
//            if (isPolyUnit(slot)) {
//                // Return true as empty value, to filter out poly ontology.
//                // TODO: Make encoder.emptyValue public, then using that consistent empty value
//                // here.
//                return context.mkTrue();
//            }
//        }
//
//        // Soft constraints for subtypeConstraint
//        Slot subtypeSlot = constraint.getSubtype();
//        Slot supertypeSlot = constraint.getSupertype();
//        IntExpr subtypeBV = subtypeSlot.serialize(this);
//        IntExpr supertypeBV = supertypeSlot.serialize(this);
//        // int weight = 1;
//        // if (subtypeSlot instanceof ConstantSlot) {
//        // weight = 2;
//        // }
//
//        addConstraint(context.mkEq(subtypeBV, supertypeBV));
//        return super.serialize(constraint);
//    }
//
//    @Override
//    public BoolExpr serialize(EqualityConstraint constraint) {
//        // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
//        // POLY_ONTOLOGY into the domain.
//        // TODO: how to encode POLY?
//        for (Slot slot : constraint.getSlots()) {
//            if (isPolyUnit(slot)) {
//                // Return true as empty value, to filter out poly ontology.
//                // TODO: Make encoder.emptyValue public, then using that consistent empty value
//                // here.
//                return context.mkTrue();
//            }
//        }
//        return super.serialize(constraint);
//    }
//
//    @Override
//    public BoolExpr serialize(InequalityConstraint constraint) {
//        // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
//        // POLY_ONTOLOGY into the domain.
//        // TODO: how to encode POLY?
//        for (Slot slot : constraint.getSlots()) {
//            if (isPolyUnit(slot)) {
//                // Return true as empty value, to filter out poly ontology.
//                // TODO: Make encoder.emptyValue public, then using that consistent empty value
//                // here.
//                return context.mkTrue();
//            }
//        }
//        return super.serialize(constraint);
//    }
//
//    protected boolean isPolyUnit(Slot slot) {
//        UnitsUtils.getInstance();
//        return slot instanceof ConstantSlot && AnnotationUtils
//                .areSameIgnoringValues(((ConstantSlot) slot).getValue(), UnitsUtils.POLYUNIT);
//    }
}
