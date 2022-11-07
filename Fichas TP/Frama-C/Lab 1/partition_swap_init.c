

void swap(int t[], int i, int j, int start, int end);



// void swap(int t[], int i, int j, int start, int end) {
//  int tmp = t[i];
//  t[i] = t[j];
//  t[j] = tmp;
// }



int partition (int A[], int p, int r) 
{ 
  int x = A[r]; 
  int j, i = p-1; 

  for (j=p; j<r; j++) 
    if (A[j] <= x) { 
      i++; 
      swap(A, i, j, p, r);
    } 
  swap(A,i+1,r,p,r);
  return i+1; 
}


