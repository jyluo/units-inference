package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

/**
 * Internal representation of a Unit, used as the core annotation mirror
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@SubtypeOf(UnknownUnits.class)
@DefaultQualifierInHierarchy
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER}) // TODO somehow make this not usable by
                                                            // users?
public @interface UnitsInternal {

    String originalName() default "default";

    boolean unknownUnits() default false;

    boolean unitsBottom() default false;

    int prefixExponent() default 0;

    BaseUnit[] baseUnits() default {};
}
