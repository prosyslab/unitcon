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
    this.s = s;
    return this.constructor;
  }
}