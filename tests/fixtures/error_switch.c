int main(){
  int x = 1;
  default: x = 1;

  switch (x) {
    int a = 3;
    case 2: break;
    case 3: case 3: break;
    case 2: break;

    default: x = 3;
    default: {
      x = a;
    }
  }
  case 3: x = 1;

  const char c = -56;
  switch (c) {
  case 200: {
    break;
  }
  case -56: {
    break;
  }
  }
}
