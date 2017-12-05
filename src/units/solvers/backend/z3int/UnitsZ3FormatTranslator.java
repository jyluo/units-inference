package units.solvers.backend.z3int;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.IntExpr;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.EqualityConstraint;
import checkers.inference.model.InequalityConstraint;
import checkers.inference.model.PreferenceConstraint;
import checkers.inference.model.Slot;
import checkers.inference.model.SubtypeConstraint;
import checkers.inference.solver.backend.z3Int.Z3IntCodec;
import checkers.inference.solver.backend.z3Int.Z3IntFormatTranslator;
import checkers.inference.solver.frontend.Lattice;

public class UnitsZ3FormatTranslator extends Z3IntFormatTranslator {

    public UnitsZ3FormatTranslator(Lattice lattice) {
        super(lattice);
    }

    @Override
    protected Z3IntCodec createZ3IntCodec() {
        return new UnitsZ3IntCodec();
    }

    @Override
    public BoolExpr serialize(SubtypeConstraint constraint) {
        // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
        // POLY_ONTOLOGY into the domain.
        // TODO: how to encode POLY?
        for (Slot slot : constraint.getSlots()) {
            if (isPolyOntology(slot)) {
                // Return true as empty value, to filter out poly ontology.
                // TODO: Make encoder.emptyValue public, then using that consistent empty value
                // here.
                return context.mkTrue();
            }
        }

        // Soft constraints for subtypeConstraint
        Slot subtypeSlot = constraint.getSubtype();
        Slot supertypeSlot = constraint.getSupertype();
        IntExpr subtypeBV = subtypeSlot.serialize(this);
        IntExpr supertypeBV = supertypeSlot.serialize(this);
        // int weight = 1;
        // if (subtypeSlot instanceof ConstantSlot) {
        // weight = 2;
        // }

        addConstraint(context.mkEq(subtypeBV, supertypeBV));
        return super.serialize(constraint);
    }

    @Override
    public BoolExpr serialize(EqualityConstraint constraint) {
        // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
        // POLY_ONTOLOGY into the domain.
        // TODO: how to encode POLY?
        for (Slot slot : constraint.getSlots()) {
            if (isPolyOntology(slot)) {
                // Return true as empty value, to filter out poly ontology.
                // TODO: Make encoder.emptyValue public, then using that consistent empty value
                // here.
                return context.mkTrue();
            }
        }
        return super.serialize(constraint);
    }

    @Override
    public BoolExpr serialize(InequalityConstraint constraint) {
        // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
        // POLY_ONTOLOGY into the domain.
        // TODO: how to encode POLY?
        for (Slot slot : constraint.getSlots()) {
            if (isPolyOntology(slot)) {
                // Return true as empty value, to filter out poly ontology.
                // TODO: Make encoder.emptyValue public, then using that consistent empty value
                // here.
                return context.mkTrue();
            }
        }
        return super.serialize(constraint);
    }

    @Override
    public BoolExpr serialize(PreferenceConstraint preferenceConstraint) {
        // Ignore constraints that contains POLY_ONTOLOGY, as currently we don't encode
        // POLY_ONTOLOGY into the domain.
        // TODO: how to encode POLY?
        for (Slot slot : preferenceConstraint.getSlots()) {
            if (isPolyOntology(slot)) {
                // Return true as empty value, to filter out poly ontology.
                // TODO: Make encoder.emptyValue public, then using that consistent empty value
                // here.
                return context.mkTrue();
            }
        }
        return super.serialize(preferenceConstraint);
    }

    protected boolean isPolyOntology(Slot slot) {
        return slot instanceof ConstantSlot && true;
        // AnnotationUtils.areSameIgnoringValues(((ConstantSlot) slot).getValue(),
        // OntologyUtils.POLY_ONTOLOGY);
    }
}
