import units.qual.*;

class ExistentialSlots {
    <T extends Number> boolean compare(T q) {
        return q == null;
    }
}
