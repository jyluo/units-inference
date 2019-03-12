package units;

import java.lang.annotation.Annotation;
import java.util.HashSet;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.AnnotationClassLoader;
import units.qual.BaseUnit;
import units.qual.UnitsAlias;

public class UnitsAnnotationClassLoader extends AnnotationClassLoader {

    protected Set<Class<? extends Annotation>> baseUnits;
    protected Set<Class<? extends Annotation>> aliasUnits;
    protected final Set<Class<? extends Annotation>> externalUnits = new HashSet<>();

    public UnitsAnnotationClassLoader(BaseTypeChecker checker) {
        super(checker);
    }

    /**
     * @return initializes and returns {@link #baseUnits}. This method is necessary as {@link
     *     #isSupportedAnnotationClass(Class)} is called during super constructor.
     */
    protected Set<Class<? extends Annotation>> getBaseUnits() {
        if (baseUnits == null) {
            baseUnits = new HashSet<>();
        }
        return baseUnits;
    }

    /**
     * @return initializes and returns {@link #aliasUnits}. This method is necessary as {@link
     *     #isSupportedAnnotationClass(Class)} is called during super constructor.
     */
    protected Set<Class<? extends Annotation>> getAliasUnits() {
        if (aliasUnits == null) {
            aliasUnits = new HashSet<>();
        }
        return aliasUnits;
    }

    /**
     * Custom filter for units annotations:
     *
     * <p>This filter will ignore (by returning false) any units annotation which is an alias of
     * another base unit annotation. Alias annotations can still be used in source code; they are
     * converted into a base annotation by {@link
     * UnitsAnnotatedTypeFactory#canonicalAnnotation(AnnotationMirror)}. This filter simply makes
     * sure that the alias annotations themselves don't become part of the type hierarchy as their
     * base annotations already are in the hierarchy.
     */
    @Override
    protected boolean isSupportedAnnotationClass(Class<? extends Annotation> annoClass) {
        if (annoClass.getAnnotation(BaseUnit.class) != null) {
            getBaseUnits().add(annoClass);
            return false;
        }
        if (annoClass.getAnnotation(UnitsAlias.class) != null) {
            getAliasUnits().add(annoClass);
            return false;
        }
        // Not an alias unit
        return true;
    }

    public void loadAllExternalUnits(String qualNames, String qualDirectories) {
        // load external individually named units
        if (qualNames != null) {
            for (String qualName : qualNames.split(",")) {
                loadExternalUnit(qualName);
            }
        }

        // load external directories of units
        if (qualDirectories != null) {
            for (String directoryName : qualDirectories.split(":")) {
                loadExternalDirectory(directoryName);
            }
        }
    }

    /** Loads and processes a single external units qualifier. */
    private void loadExternalUnit(String annoName) {
        // loadExternalAnnotationClass() returns null for alias units
        Class<? extends Annotation> loadedClass = loadExternalAnnotationClass(annoName);
        if (loadedClass != null) {
            externalUnits.add(loadedClass);
        }
    }

    /** Loads and processes the units qualifiers from a single external directory. */
    private void loadExternalDirectory(String directoryName) {
        Set<Class<? extends Annotation>> annoClassSet =
                loadExternalAnnotationClassesFromDirectory(directoryName);

        for (Class<? extends Annotation> loadedClass : annoClassSet) {
            externalUnits.add(loadedClass);
        }
    }

    /** @return the set of externally loaded units */
    public Set<? extends Class<? extends Annotation>> getExternalUnits() {
        return externalUnits;
    }
}
