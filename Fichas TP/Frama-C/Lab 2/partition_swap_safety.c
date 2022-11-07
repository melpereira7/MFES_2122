

// Note: without the assigns clauses one would be forced
// to include \valid(A+(p..r)) in the loop invariant

// && start <= i <= end && start <= j <= end;





/*@ requires \valid(t+(start..end)) && start <= i <= end && start <= j <= end;
  @ assigns t[i], t[j];
  @*/
void swap(int t[], int i, int j, int start, int end);


/* void swap(int t[], int i, int j, int start, int end) { */
/*     int tmp = t[i]; */
/*     t[i] = t[j]; */
/*     t[j] = tmp; */
/* } */

void swap(int t[], int i, int j, int start, int end) {
  t[i] += t[j];
  t[j] = t[i]-t[j];
  t[i] -= t[j];
}



/*@ requires 0 <= p <= r && \valid(A+(p..r));
  @*/
int partition (int A[], int p, int r) 
{ 
  int x = A[r]; 
  int j, i = p-1; 

  /*@ loop invariant p <= j <= r && p-1 <= i < j;
    @ loop assigns i, j, A[p..r-1];
    @ loop variant r-j;
    @*/
  for (j=p; j<r; j++) 
    if (A[j] <= x) { 
      i++; 
      swap(A,i,j,p,r);
    } 
  swap(A,i+1,r,p,r);
  return i+1; 
}


