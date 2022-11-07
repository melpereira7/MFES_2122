

#define LENGTH 100
int vec[LENGTH];

int maxarray(int u[], int size) { ... }

void main() { 
  int max;
  max = maxarray(vec, LENGTH);

  /*@ assert 0 <= max < LENGTH &&
    @       (\forall int a; 0 <= a < LENGTH ==> vec[a] <= vec[max]);
    @*/  
}
