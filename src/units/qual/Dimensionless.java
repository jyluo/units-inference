package units.qual;

import static org.checkerframework.framework.qual.LiteralKind.BOOLEAN;
import static org.checkerframework.framework.qual.LiteralKind.CHAR;
import static org.checkerframework.framework.qual.LiteralKind.DOUBLE;
import static org.checkerframework.framework.qual.LiteralKind.FLOAT;
import static org.checkerframework.framework.qual.LiteralKind.INT;
import static org.checkerframework.framework.qual.LiteralKind.LONG;
import static org.checkerframework.framework.qual.LiteralKind.STRING;
import static org.checkerframework.framework.qual.TypeUseLocation.EXCEPTION_PARAMETER;
import static org.checkerframework.framework.qual.TypeUseLocation.LOCAL_VARIABLE;
import static org.checkerframework.framework.qual.TypeUseLocation.PARAMETER;
import static org.checkerframework.framework.qual.TypeUseLocation.RESOURCE_VARIABLE;
import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.DefaultFor;
import org.checkerframework.framework.qual.ImplicitFor;
import org.checkerframework.framework.qual.SubtypeOf;

/**
 * A dimensionless "unit".
 *
 * @checker_framework.manual #units-checker Units Checker
 */
@SubtypeOf(UnknownUnits.class)
@DefaultFor({
        // exceptions are always dimensionless
        EXCEPTION_PARAMETER,
        // most user classes are dimensionless, and when used as a local reference there will be
        // many type.invalid errors, this is a better default, where any variable that should be
        // refined can be tagged UnknownUnits
        LOCAL_VARIABLE, // this somehow also applies to enhanced for loop variables
        RESOURCE_VARIABLE, PARAMETER,})
@ImplicitFor(literals = {INT, LONG, FLOAT, DOUBLE, BOOLEAN, CHAR, STRING}, // not sure that literals
                                                                           // need to be impliclty
                                                                           // declared
        typeNames = {Throwable.class, Exception.class, Class.class})
@UnitsAlias({0, 0})
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface Dimensionless {
}
