package units;

import java.lang.annotation.Annotation;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.AnnotationClassLoader;
import units.qual.IsBaseUnit;
import units.qual.UnitsAlias;
import units.representation.UnitsRepresentationUtils;

public class UnitsAnnotationClassLoader extends AnnotationClassLoader {

    public UnitsAnnotationClassLoader(BaseTypeChecker checker) {
        super(checker);
    }

    /**
     * Custom filter for units annotations:
     *
     * <p>
     * This filter will ignore (by returning false) any units annotation which is an alias of
     * another base unit annotation. Alias annotations can still be used in source code; they are
     * converted into a base annotation by
     * {@link UnitsAnnotatedTypeFactory#aliasedAnnotation(AnnotationMirror)}. This filter simply
     * makes sure that the alias annotations themselves don't become part of the type hierarchy as
     * their base annotations already are in the hierarchy.
     */
    @Override
    protected boolean isSupportedAnnotationClass(Class<? extends Annotation> annoClass) {

        if (annoClass.getAnnotation(IsBaseUnit.class) != null) {
            UnitsRepresentationUtils.addBaseUnit(annoClass.getSimpleName());
            return false;
        }

        if (annoClass.getAnnotation(UnitsAlias.class) != null) {
            return false;
        }

        // Not an alias unit
        return true;
    }
}
