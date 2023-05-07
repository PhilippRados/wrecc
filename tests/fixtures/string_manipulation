char* malloc(int size);
void printf(char* s, char* str);
void strcpy(char* p, char* s);
long strlen(char* s);
int snprintf(char* s, int len, char* f, int d);

void reverseString(char* s, int sSize) {
  if (sSize <= 1)
    return;
  int left = 0;
  int right = sSize - 1;

  char temp = s[left];
  s[left] = s[right];
  s[right] = temp;

  reverseString(s + 1, sSize - 2);
}

int isInterleave(char* s1, char* s2, char* s3) {
  int m = strlen(s1);
  int n = strlen(s2);
  int l = strlen(s3);

  if ((m + n) != l)
    return 0;

  int dp[6][6];

  for (int x = 0; x <= m; x = x + 1) {
    for (int y = 0; y <= n; y = y + 1) {
      dp[x][y] = 0;
    }
  }

  for (int i = 0; i <= m; i = i + 1) {
    for (int j = 0; j <= n; j = j + 1) {
      if (i == 0 && j == 0)
        dp[i][j] = 1;
      else if (i == 0)
        dp[i][j] = dp[i][j - 1] && s2[j - 1] == s3[j - 1];
      else if (j == 0) {
        dp[i][j] = dp[i - 1][j] && s1[i - 1] == s3[i - 1];

        }
      else
        dp[i][j] = (dp[i][j - 1] && s2[j - 1] == s3[i + j - 1]) || (dp[i - 1][j] && s1[i - 1] == s3[i + j - 1]);
    }
  }

  return dp[m][n];
}

int main() {
  char* some = malloc(10);
  strcpy(some, "something");
  reverseString(some, 9);

  printf("reverse: %s\n", some);

  char* s1 = malloc(6);
  char* s2 = malloc(6);
  char* s3 = malloc(10);

  strcpy(s1, "aabcc");
  strcpy(s2, "dbbca");
  strcpy(s3, "aadbbcbcac");

  char* result = malloc(10);
  if (isInterleave(s1, s2, s3)) {
    result = "true";
  } else {
    result = "false";
  }

  printf("interleave: %s\n", result);
}
