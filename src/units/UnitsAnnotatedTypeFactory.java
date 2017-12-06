package units;

import java.lang.annotation.Annotation;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ImplicitsTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.GraphQualifierHierarchy;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import com.sun.source.tree.BinaryTree;
import units.qual.UnitsAlias;
import units.qual.UnitsBottom;
import units.qual.UnknownUnits;
import units.util.UnitsUtils;

public class UnitsAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {

    protected final AnnotationMirror UNKNOWNUNITS =
            AnnotationBuilder.fromClass(elements, UnknownUnits.class);
    protected final AnnotationMirror BOTTOM =
            AnnotationBuilder.fromClass(elements, UnitsBottom.class);

    public UnitsAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
        // Use the Units Annotated Type Loader instead of the default one
        loader = new UnitsAnnotationClassLoader(checker);

        // get all the loaded annotations
        Set<Class<? extends Annotation>> qualSet = new HashSet<Class<? extends Annotation>>();
        qualSet.addAll(getBundledTypeQualifiersWithPolyAll());

//        // load all the external units
//        loadAllExternalUnits();
//
//        // copy all loaded external Units to qual set
//        qualSet.addAll(externalQualsMap.values());

        return qualSet;
    }
    
    @Override
    public AnnotationMirror aliasedAnnotation(AnnotationMirror anno) {
        for (AnnotationMirror metaAnno : anno.getAnnotationType().asElement().getAnnotationMirrors()) {
            if(AnnotationUtils.areSameByClass(metaAnno, UnitsAlias.class)) {
                
                Map<String, Integer> exponents = new TreeMap<>();
                exponents.put("m", 1);
                exponents.put("s", 1);
                
                return UnitsUtils.createInternalUnit("dummy", 1, exponents);
            }
        }
        
        return super.aliasedAnnotation(anno);
    }
    
    @Override
    public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
        return new UnitsQualifierHierarchy(factory, BOTTOM);
    }

    private final class UnitsQualifierHierarchy extends GraphQualifierHierarchy {

        public UnitsQualifierHierarchy(MultiGraphFactory mgf, AnnotationMirror bottom) {
            super(mgf, bottom);
        }
    }

    // @Override
    // protected void addCheckedCodeDefaults(QualifierDefaults defaults) {
    // TypeUseLocation[] topLocations = {TypeUseLocation.ALL};
    // defaults.addCheckedCodeDefaults(OntologyUtils.ONTOLOGY_TOP, topLocations);
    // }

    @Override
    public TreeAnnotator createTreeAnnotator() {
        return new ListTreeAnnotator(
                new UnitsPropagationTreeAnnotator(), new ImplicitsTreeAnnotator(this));
    }

    public class UnitsPropagationTreeAnnotator extends PropagationTreeAnnotator {
        public UnitsPropagationTreeAnnotator() {
            super(UnitsAnnotatedTypeFactory.this);
        }

        @Override
        public Void visitBinary(BinaryTree node, AnnotatedTypeMirror type) {
            // TODO: Type checking rules, same as standard Units ATF
            return super.visitBinary(node, type);
        }
    }
}
