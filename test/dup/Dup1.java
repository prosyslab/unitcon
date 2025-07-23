public class Dup1 extends Dup {
  int i, j, k, l;

  public Dup1(int i) {
    this(i, 0);

  }
  public Dup1(int i, int j) {
    this(i, j, 0);

  }

  public Dup1(int i, int j, int k) {
    this(i, j, k, 0);

  }

  public Dup1(int i, int j, int k, int l) {
    super(i, j, k, l);
  }
}
