public class Dup {
  int i, j, k, l;

  protected Dup(int i) {
    this(i, 0);

  }
  protected Dup(int i, int j) {
    this(i, j, 0);

  }

  protected Dup(int i, int j, int k) {
    this(i, j, k, 0);

  }

  protected Dup(int i, int j, int k, int l) {
    this.i = i;
    this.j = j;
    this.k = k;
    this.l = l;
  }

  public Object getObject(int k) {
    if (k >= 25) {
      return null;
    }
    return new Object();
  }
}
