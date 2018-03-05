import units.qual.*;

class ClassTypeParam<T> {
    T q;
    T r;

    ClassTypeParam(T q, T r) {
        this.q = q;
        this.r = r;
    }

    @Override
    public String toString() {
        return "<Q=" + q + " R=" + r + ">";
    }
}

class ClassTypeParamTwo<T extends Number> {
    T q;
    T r;

    ClassTypeParamTwo(T q, T r) {
        this.q = q;
        this.r = r;
    }

    @Override
    public String toString() {
        return "<Q=" + q + " R=" + r + ">";
    }
}
