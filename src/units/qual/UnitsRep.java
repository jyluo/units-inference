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
@SubtypeOf({})
@DefaultQualifierInHierarchy
@Documented
@Retention(RetentionPolicy.RUNTIME)
// TODO somehow make this not usable by users?
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface UnitsRep {

    // TODO: remove name
    String originalName() default "default";

    boolean top() default false;

    boolean bot() default false;

    int prefixExponent() default 0;

    BUC[] baseUnitComponents() default {};
}
