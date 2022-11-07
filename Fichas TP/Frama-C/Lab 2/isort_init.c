

/*@ predicate sorted(int *t,integer i,integer j) =
  @   ...
  @*/

/*@ requires N>0  && \valid(A+(0..N-1));
  @ assigns A[0..N-1];
  @ ensures sorted(A,0,N-1);
  @*/
void insertionSort(int A[], int N) {
    int i, j, key;    
    for (j=1 ; j<N ; j++) {
        key = A[j];
        i = j-1;        
        while (i>=0 && A[i] > key) {
            A[i+1] = A[i];
            i--;
        }
        A[i+1] = key;
    }
}
