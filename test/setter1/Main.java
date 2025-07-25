public class Main {
  Object obj = new Object();
  public void setObj(Object obj) {
    this.obj = obj;
  }

  public void errorMethod(int i, int j) {
    if (i > 10) {
      obj.toString();
    }
  }
}
