

/*@ logic integer fact (integer n) = 
  @ (n == 0) ? 1 : n * fact(n-1);
  @ 
  @*/ 






/*@ requires n >= 0;
  @ ensures \result == fact(n);
  @ assigns \nothing;
  @*/
int factf (int n);




/*@ requires \valid(factable+(0..size-1)) && size>0;
  @ assigns  factable[0..size-1];
  @ ensures 
  @    \forall integer a ; 0 <= a < size ==>  factable[a] == fact (a);
  @*/
void factab (int factable[], int size)
{
  int k = 0 ; 

  while (k < size) {
    factable[k] = factf(k) ; 
    k++;
  }
}

