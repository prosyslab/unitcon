package example;

import java.lang.IllegalArgumentException;

public class Checker {

  boolean done = false;
  char prefixChar = 'a';
  int expectedLength = 0;

  public void setExpectedLength(int expectedLength) {
    this.expectedLength = expectedLength;
  } 

  public boolean checkAlphabet(String string) {
    boolean check = false;

    if (this.expectedLength < 10) {
      return false;
    }

    switch (string.charAt(0)) {
    case 'a':
      if (string.length() == 1) {
        throw new IllegalArgumentException();
      }
      else if (string.charAt(1) == 'b') {
        check = true;
      }
      break;
    default:
      break;
    }

    return check;
  }
}