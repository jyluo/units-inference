import units.qual.*;

/**
* Class to represent a QR decomposition.
*
* @param <T>
*/
class QRDecomposition<T> {
    public T q;
    public T r;

    QRDecomposition(T q, T r) {
        this.q = q;
        this.r = r;
    }

    @Override
    public String toString() {
        return "<Q=" + q + " R=" + r + ">";
    }
}