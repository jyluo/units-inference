import units.qual.*;

class GenericClass<T> {
    T q;
    T r;

    GenericClass(T q, T r) {
        this.q = q;
        this.r = r;
    }

    T getQ() {
        return q;
    }

    T getR() {
        return r;
    }

    boolean compareNullL(T q) {
        return null == q;
    }

    boolean compareNullR(T q) {
        return q == null;
    }

    boolean compare(T q, T r) {
        return q == r;
    }

    // TODO: make it so users don't have to manually state @UnknownUnits this
    @Override
    public String toString(@UnknownUnits GenericClass<T> this) {
        return "<Q=" + q + " R=" + r + ">";
    }
}

class GenericClassTwo<T extends Number> {
    T q;
    T r;

    GenericClassTwo(T q, T r) {
        this.q = q;
        this.r = r;
    }

    T getQ() {
        return q;
    }

    T getR() {
        return r;
    }

    boolean compareNullL(T q) {
        return null == q;
    }

    boolean compareNullR(T q) {
        return q == null;
    }

    boolean compare(T q, T r) {
        return q == r;
    }

    // TODO: make it so users don't have to manually state @UnknownUnits this
    @Override
    public String toString(@UnknownUnits GenericClassTwo<T> this) {
        return "<Q=" + q + " R=" + r + ">";
    }
}
