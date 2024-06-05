// A8Q2 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

method A8Q1(x: int, y: int, z: int) returns (m: int)
/*Pre-Condition*/   requires true;
/*Post-Condition*/  ensures m<=x && m<=y && m<=z;
{ 
  /* (| true |)                               - Pre-Condition */
      if(z<y){
      /* (| z<y |)                            - if-then-else  */   
          if(z<x){
            /* (| z<y ^ z<=x |)               - if-then-else  */  
            /* (| z<=x ^ z<=y ^ z<=z |)       - implied (a)   */  
                m := z;
            /* (| m<=x ^ m<=y ^ m<=z |)       - assignment    */  
          }else{
            /* (| z<y ^ -(z<=x) |)            - if-then-else  */  
            /* (| x<=x ^ x<=y ^ x<=z |)       - implied (b)   */  
                m := x;
            /* (| m<=x ^ m<=y ^ m<=z |)       - assignment    */  
          }
      }else{
      /* (| -(z<y) |)                         - if-then-else  */  
      /* (| y<=y ^ y<=z |)                    - implied (c)   */  
          m := y;
      /* (| m<=y ^ y<=z |)                    - assignment    */  
          if (x<y){
            /* (| m<=y ^ y<=z ^ x<y |)        - if-then       */  
            /* (| x<=x ^ x<=y ^ x<=z |)       - implied (d)   */  
                m := x;
            /* (| m<=x ^ m<=y ^ m<=z |)       - assignment    */  
          }
      /* (| m<=x ^ m<=y ^ m<=z |)             - if-then: implied (e) */  
      }
  /* (| m<=x ^ m<=y ^ m<=z |)                 - if-then-else  */  
}

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/

