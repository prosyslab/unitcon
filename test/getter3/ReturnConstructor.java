public class ReturnConstructor {
  int i;
  double d;
  String s;
  Constructor constructor;

  public Constructor getConstructor() {
    return this.constructor;
  }

  public Constructor getConstructor(int i) {
    this.i = i;
    return this.constructor;
  }

  public Constructor getConstructor(double d) {
    this.d = d;
    return this.constructor;
  }

  public Constructor getConstructor(String s) {
    short p = 0;
    this.constructor = new Constructor(0, 0f, 0, 0d, "", null, false, p);
    return this.constructor;
  }

  public void setConstructor(Constructor c) {
    this.constructor = c;
  }
}