void printf(char* s, int d);
long strlen(char* s);

char* name(int age, int color){
  printf("age:%d\n",age);
  printf("color:%d\n",color);
  
  return "otto";
}
int more(long e,int d, char w, int a, long f, int u, int h){
  printf("%d\n",e);
  printf("%d\n",d);
  printf("%d\n",w);
  printf("%d\n",a);
  printf("%d\n",f);
  printf("%d\n",u);
  printf("%d\n",h);

  return e + d + w * a - f % u - h;
}

char some(char* s,long sec, int third){
  return strlen(s);
}

int main(){
  printf("assert: %d\n",more(strlen(name(4,2)),some("uwe",13,19), 12, 4, 3, 8, 14));
}
