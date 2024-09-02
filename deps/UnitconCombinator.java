public class UnitconCombinator {
  public static short[] combineShort(short[] seed) {
    return seed;
  }

  public static byte[] combineByte(byte[] seed) {
    return seed;
  }

  public static char[] combineChar(char[] seed) {
    return seed;
  }

  public static boolean[] combineBool(boolean[] seed) {
    return seed;
  }

  public static int[] combineInt(int[] seed) {
    int countIgnore = 0;

    for (int i = 0; i < seed.length; i++) {
      if (seed[i] == 0) {
        countIgnore++;
      }
    }

    int length = seed.length + (seed.length - countIgnore) * (seed.length - countIgnore);

    int[] result = new int[length];
    int totalIndex = 0;

    for (int i = 0; i < seed.length; i++) {
      for (int j = 0; j < seed.length; j++) {
        if (i == j) {
          result[totalIndex++] = seed[i];
        }
        if (seed[i] == 0 || seed[j] == 0) {
          continue;
        }
        result[totalIndex++] = seed[i] + seed[j];
      }
    }
    return result;
  }

  public static long[] combineLong(long[] seed) {
    int countIgnore = 0;

    for (int i = 0; i < seed.length; i++) {
      if (seed[i] == 0) {
        countIgnore++;
      }
    }

    int length = seed.length + (seed.length - countIgnore) * (seed.length - countIgnore);

    long[] result = new long[length];
    int totalIndex = 0;

    for (int i = 0; i < seed.length; i++) {
      for (int j = 0; j < seed.length; j++) {
        if (i == j) {
          result[totalIndex++] = seed[i];
        }
        if (seed[i] == 0L || seed[j] == 0L) {
          continue;
        }
        result[totalIndex++] = seed[i] + seed[j];
      }
    }
    return result;
  }

  public static float[] combineFloat(float[] seed) {
    int countIgnore = 0;

    for (int i = 0; i < seed.length; i++) {
      if (seed[i] == 0) {
        countIgnore++;
      }
    }

    int length = seed.length + (seed.length - countIgnore) * (seed.length - countIgnore);

    float[] result = new float[length];
    int totalIndex = 0;

    for (int i = 0; i < seed.length; i++) {
      for (int j = 0; j < seed.length; j++) {
        if (i == j) {
          result[totalIndex++] = seed[i];
        }
        if (seed[i] == 0.0f || seed[j] == 0.0f) {
          continue;
        }
        result[totalIndex++] = seed[i] + seed[j];
      }
    }
    return result;
  }

  public static double[] combineDouble(double[] seed) {
    int countIgnore = 0;

    for (int i = 0; i < seed.length; i++) {
      if (seed[i] == 0) {
        countIgnore++;
      }
    }

    int length = seed.length + (seed.length - countIgnore) * (seed.length - countIgnore);

    double[] result = new double[length];
    int totalIndex = 0;

    for (int i = 0; i < seed.length; i++) {
      for (int j = 0; j < seed.length; j++) {
        if (i == j) {
          result[totalIndex++] = seed[i];
        }
        if (seed[i] == 0.0 || seed[j] == 0.0) {
          continue;
        }
        result[totalIndex++] = seed[i] + seed[j];
      }
    }
    return result;
  }

  public static String[] combineString(String[] seed) {
    int countIgnore = 0;

    for (int i = 0; i < seed.length; i++) {
      if (seed[i] == null || seed[i] == "") {
        countIgnore++;
      }
    }

    int length = seed.length + (seed.length - countIgnore) * (seed.length - countIgnore);

    String[] result = new String[length];
    int totalIndex = 0;

    for (int i = 0; i < seed.length; i++) {
      for (int j = 0; j < seed.length; j++) {
        if (i == j) {
          result[totalIndex++] = seed[i];
        }
        if (seed[i] == null || seed[i] == "" || seed[j] == null || seed[j] == "") {
          continue;
        }
        result[totalIndex++] = seed[i] + seed[j];
      }
    }
    return result;
  }
}