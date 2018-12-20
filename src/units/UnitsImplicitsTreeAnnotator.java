package units;

import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.MemberSelectTree;
import javax.lang.model.element.Name;
import org.checkerframework.framework.qual.LiteralKind;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import units.representation.UnitsRepresentationUtils;

/** Common base class for ImplicitsTreeAnnotator. */
public abstract class UnitsImplicitsTreeAnnotator extends ImplicitsTreeAnnotator {

    UnitsRepresentationUtils unitsRepUtils = UnitsRepresentationUtils.getInstance();

    // Programmatically set the qualifier implicits
    public UnitsImplicitsTreeAnnotator(AnnotatedTypeFactory atf) {
        super(atf);

        // set BOTTOM as the implicit qualifier for null literals
        addLiteralKind(LiteralKind.NULL, unitsRepUtils.BOTTOM);
        addLiteralKind(LiteralKind.STRING, unitsRepUtils.DIMENSIONLESS);
        addLiteralKind(LiteralKind.CHAR, unitsRepUtils.DIMENSIONLESS);
        addLiteralKind(LiteralKind.BOOLEAN, unitsRepUtils.DIMENSIONLESS);
    }

    // this is called if the enum constant is directly used via a static import
    @Override
    public Void visitIdentifier(IdentifierTree node, AnnotatedTypeMirror atm) {
        super.visitIdentifier(node, atm);
        replaceEnumConstantType(node.getName(), atm);
        return null;
    }

    // this is called if the enum constant is used via Type.Constant
    @Override
    public Void visitMemberSelect(MemberSelectTree node, AnnotatedTypeMirror atm) {
        super.visitMemberSelect(node, atm);
        replaceEnumConstantType(node.getIdentifier(), atm);
        return null;
    }

    abstract void replaceEnumConstantType(Name name, AnnotatedTypeMirror atm);
}
