package units.qual;

import static org.checkerframework.framework.qual.TypeUseLocation.EXPLICIT_LOWER_BOUND;
import static org.checkerframework.framework.qual.TypeUseLocation.EXPLICIT_UPPER_BOUND;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.TargetLocations;

/**
 * The bottom type in the Units type system. Programmers should rarely write this type.
 *
 * @checker_framework.manual #units-checker Units Checker
 * @checker_framework.manual #bottom-type the bottom type
 */
// @ImplicitFor(types = {TypeKind.VOID, TypeKind.NULL},
// typeNames = Void.class,
// literals = LiteralKind.NULL)
// @DefaultFor({LOWER_BOUND})
@UnitsAlias(baseUnitComponents = {})
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@TargetLocations({EXPLICIT_LOWER_BOUND, EXPLICIT_UPPER_BOUND})
public @interface UnitsBottom {}
