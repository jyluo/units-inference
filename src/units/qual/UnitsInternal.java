package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.SubtypeOf;

/**
 * Internal representation of a Unit
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER}) // TODO fix
@SubtypeOf(UnknownUnits.class)
public @interface UnitsInternal {
    String originalName() default "default";
    int prefixExponent() default 0;

    // only primitive type, String, Class, annotation, enumeration are permitted or 1-dimensional arrays thereof
    // int[], fast access, ordering must be enforced internally (sorted by base unit names)
    // annotation[], ... O(n) access, order does not matter, safer, but can't work with AnnotationBuilder
    // BaseUnitExpo[] exponents();
    
    int[] exponents();
}
