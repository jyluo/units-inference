package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

/**
 * Internal representation of a Unit
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@SubtypeOf(UnknownUnits.class)
@DefaultQualifierInHierarchy
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER}) // TODO fix
public @interface UnitsInternal {

    String originalName() default "default";

    boolean unknownUnits() default false;

    boolean unitsBottom() default false;

    int prefixExponent() default 0;

    // only primitives, String, Class, annotation, enumeration are permitted or 1D arrays thereof
    BaseUnit[] baseUnits() default {};
}
