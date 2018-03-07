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

    @Override
    public String toString() {
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

    @Override
    public String toString() {
        return "<Q=" + q + " R=" + r + ">";
    }
}
