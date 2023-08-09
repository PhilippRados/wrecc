void printf(char* format, int input);

int main(){
    int a = 0 || 0;
    printf("%d\n",a);
    int b = 0 || 1;
    printf("%d\n",b);
    int c = 1 || 0;
    printf("%d\n",c);
    int d = 1 || 1;
    printf("%d\n",d);

    int e = 0 && 0;
    printf("%d\n",e);
    int f = 0 && 1;
    printf("%d\n",f);
    int g = 1 && 0;
    printf("%d\n",g);
    int h = 1 && 1;
    printf("%d\n",h);
}
