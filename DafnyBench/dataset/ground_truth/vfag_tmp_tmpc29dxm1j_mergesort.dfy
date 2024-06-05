method ordenar_mergesort(V : array?<int>)

    requires V != null
    
    modifies V

{
    
    mergesort(V, 0, V.Length - 1) ;
    
}



method mergesort(V : array?<int>, c : int, f : int) 

    requires V != null
    requires c >= 0 && f <= V.Length
    
    decreases f - c

    modifies V

{
    
    if c < f {
        
        var m : int ;
	m := c + (f - c) / 2 ;
        
        mergesort(V, c, m) ;
        mergesort(V, m + 1, f) ;

        mezclar(V, c, m, f) ;
        
    }
    
}



method mezclar(V: array?<int>, c : int, m : int, f : int)

    requires V != null
    requires c <= m <= f
    requires 0 <= c <= V.Length
    requires 0 <= m <= V.Length
    requires 0 <= f <= V.Length

    modifies V

{

    var V1 : array?<int> ;
    var j  : nat ;

    V1 := new int[m - c + 1] ;
    j  := 0 ;
    
    while j < V1.Length && c + j < V.Length
        
        invariant 0 <= j     <= V1.Length
        invariant 0 <= c + j <= V.Length
        
        decreases V1.Length - j
        
    {

            V1[j] := V[c + j] ;
            j := j + 1 ;
            
    }


    var V2 : array?<int> ;
    var k  : nat ;

    V2 := new int[f - m] ; 
    k  := 0 ;
    
    while k < V2.Length && m + k + 1 < V.Length
    
        invariant 0 <= k     <= V2.Length
        invariant 0 <= m + k <= V.Length
        
        decreases V2.Length - k
        
    {
        
        V2[k] := V[m + k + 1] ;
        k := k + 1 ;
        
    }


    var i : nat ;

    i := 0 ;
    j := 0 ;
    k := 0 ;
    
    while i < f - c + 1  && 
          j <= V1.Length && 
          k <= V2.Length && 
          c + i < V.Length
    
        invariant 0 <= i <= f - c + 1
        
        decreases f - c - i
        
    {
        
        if j >= V1.Length && k >= V2.Length {
            
            break ;
            
        }
        
        else if j >= V1.Length {
            
            V[c + i] := V2[k] ;
            k := k + 1 ;
            
        }
        
        else if k >= V2.Length {
            
            V[c + i] := V1[j] ;
            j := j + 1 ;
            
        }
        
        else {
            
            if V1[j] <= V2[k] {
                
                V[c + i] := V1[j] ;
                j := j + 1 ;
                
            }
            
            else if V1[j] > V2[k] {
                
                V[c + i] := V2[k] ;
                k := k + 1 ;
                
            }
            
        }
        
        i := i + 1 ;
        
    }
    
}
