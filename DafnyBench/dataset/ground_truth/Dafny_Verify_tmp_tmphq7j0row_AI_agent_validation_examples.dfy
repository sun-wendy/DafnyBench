function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{
    y := 1;
    var x := 0; 
    while x != N
        invariant 0 <= x <= N 
        invariant y == Power(x) 
        decreases N - x
    {
        x, y := x + 1, y + y;
    } 
}


// Original davinci-003 completion:
// method ComputePower1(N: int) returns (y: nat) requires N >= 0
//     ensures y == Power(N)
// {
//     y := 1;
//     var x := 0; 
//     while x != N
//         decreases N - x
//         invariant 0 <= x <= N
//         invariant y == Power(x)
//     {
//         x, y := x + 1, y + y;
//     }
// }



// Fine_tuned davinci-003 completion:
// method ComputePower1(N: int) returns (y: nat) requires N >= 0
//     ensures y == Power(N)
// {
//     y := 1;
//     var x := 0; 
//     while x != N
//         decreases N - x
//         invariant 0 <= x <= N
//         invariant y == Power(x)
//     {
//         x, y := x + 1, y + y;
//     }
// }

method Max(a: array<nat>) returns (m: int)
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
    m := 0;
    var n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> a[i] <= m
        invariant (m == 0 && n == 0) || exists i :: 0 <= i < n && m == a[i]
    {
        if m < a[n] {
            m := a[n]; 
        }
        n := n + 1; 
    }
}

// Original davinci-003 completion:
// method Max(a: array<nat>) returns (m: int)
//     requires a.Length > 0
//     ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
//     ensures exists i :: 0 <= i < a.Length && m == a[i] 
// {
//     m := a[0];
//     var n := 1;
//     while n != a.Length
//     {
//         if m < a[n] {
//             m := a[n]; 
//         }
//         n := n + 1; 
//         // Loop invariant: 0 <= n <= a.Length && forall i :: 0 <= i < n ==> a[i] <= m
//     }
// }

// Fine_tuned davinci-003 completion:
// method Max1(a: array<nat>) returns (m: int)
//     ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
//     ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i]
// {
//     m := 0;
//     var n := 0;
//     while n != a.Length
//         invariant 0 <= n <= a.Length
//         invariant forall i :: 0 <= i < n ==> a[i] <= m
//     {
//         if m < a[n] {
//             m := a[n]; 
//         }
//         n := n + 1; 
//     }
// }

method Cube(n: nat) returns (c: nat) 
    ensures c == n * n * n
{
    c := 0;
    var i := 0;
    var k := 1;
    var m := 6;
    while i != n
        invariant 0 <= i <= n 
        invariant c == i * i * i 
        invariant k == 3*i*i + 3*i + 1
        invariant m == 6 * i + 6
    {
        c, k, m := c + k, k + m, m + 6; 
        i := i + 1;
    }
}

// Original davinci-003 completion:
// method Cube(n: nat) returns (c: nat) 
//     ensures c == n * n * n
// {
//     c := 0;
//     var i := 0;
//     var k := 1;
//     var m := 6;
//     // Loop invariant: c = i^3
//     while i != n
//     {
//         c, k, m := c + k, k + m, m + 6; 
//         i := i + 1;
//     }
// }

// Fine_tuned davinci-003 completion:
// method Cube1(n: nat) returns (c: nat) 
//     ensures c == n * n * n
// {
//     c := 0;
//     var i := 0;
//     var k := 1;
//     var m := 6;
//     while i != n
//         invariant 0 <= i <= n
//         invariant c == i * k * m
//     {
//         c, k, m := c + k, k + m, m + 6; 
//         i := i + 1;
//     }
// }



method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
    var m := 0;
    while m != a.Length0
        invariant 0 <= m <= a.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1 
        invariant forall i, j :: m <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
    {
        var n := 0;
        while n != a.Length1
            invariant 0 <= n <= a.Length1
            invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1 
            invariant forall i, j :: m < i < a.Length0 && 0 <= j < a.Length1==> a[i,j] == old(a[i,j]) 
            invariant forall j :: 0 <= j < n ==> a[m,j] == old(a[m,j])+1
            invariant forall j :: n <= j < a.Length1 ==> a[m,j] == old(a[m,j])
        {
            a[m,n] := a[m,n] + 1;
            n := n + 1; 
        }
        m := m + 1; 
    }
}

// Original davinci-003 completion:
// method IncrementMatrix(a: array2<int>)
//     modifies a
//     ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
// {
//     var m := 0;
//     while m != a.Length0
//     {
//         var n := 0;
//         while n != a.Length1
//         {
//             // Loop invariant: forall i, j :: 0 <= i < m && 0 <= j < n ==> a[i,j] == old(a[i,j]) + 1
//             a[m,n] := a[m,n] + 1;
//             n := n + 1; 
//         }
//         m := m + 1; 
//     }
// }

// Fine_tuned davinci-003 completion:
// method IncrementMatrix1(a: array2<int>)
//     modifies a
//     ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
// {
//     var m := 0;
//     while m != a.Length0
//         invariant 0 <= m <= a.Length0 && 0 <= j < a.Length1 <= a.Length2
//         invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
//     {
//         var n := 0;
//         while n != a.Length1
//         invariant 0 <= n <= a.Length2
//         invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
//         {
//             a[m,n] := a[m,n] + 1;
//         n := n + 1; 
//         }
//         m := m + 1; 
//     }
// }

method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
    var m := 0;
    while m != src.Length0
        invariant 0 <= m <= src.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
        invariant forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i,j] == old(src[i,j])
    {
        var n := 0;
        while n != src.Length1
            invariant 0 <= n <= src.Length1 
            invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
            invariant forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i,j] == old(src[i,j])
            invariant forall j :: 0 <= j < n ==> dst[m,j] == old(src[m,j])
        {
            dst[m,n] := src[m,n]; n := n + 1;
        }
        m := m + 1; 
    }
}

// Original davinci-003 completion:
// method CopyMatrix(src: array2, dst: array2)
//     requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//     modifies dst
//     ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
// {
//     var m := 0;
//     while m != src.Length0
//     {
//         var n := 0;
//         while n != src.Length1
//         {
//             dst[m,n] := src[m,n]; 
//             n := n + 1;
//             // Loop invariant: forall i, j :: 0 <= i < m && 0 <= j < n ==> dst[i,j] == old(src[i,j])
//         }
//         m := m + 1; 
//     }
// }

// Fine_tuned davinci-003 completion:
// method CopyMatrix1(src: array2, dst: array2)
//     requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//     modifies dst
//     ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
//     var m := 0;
//     while m != src.Length0
//         invariant 0 <= m <= src.Length0
//         invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
//     {
//         var n := 0;
//         while n != src.Length1
//            invariant 0 <= n <= src.Length1
//         {
//            dst[m,n] := src[m,n]; n := n + 1;
//         }
//         m := m + 1; 
//     }




method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
    var n := 0;
    while n != src.Length
    invariant 0 <= n <= src.Length
    invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i]) 
    invariant forall i :: n <= i < src.Length ==> src[i] == old(src[i])
    {
        dst[n] := 2 * src[n]; n := n + 1;
    } 
}

// Original davinci-003 completion:
// method DoubleArray(src: array<int>, dst: array<int>)
//     requires src.Length == dst.Length
//     modifies dst
//     ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// {
//     var n := 0;
//     var i : int := 0;
//     while n != src.Length
//     {
//         dst[n] := 2 * src[n];
//         n := n + 1;
//         i := i + 1;
//     } 
//     assert i == src.Length;
// }

// Fine_tuned davinci-003 completion:
// method DoubleArray1(src: array<int>, dst: array<int>)
//     requires src.Length == dst.Length
//     modifies dst
//     ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// {
//     var n := 0;
//     while n != src.Length
//         invariant 0 <= n <= src.Length
//         invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
//     {
//         dst[n] := 2 * src[n]; n := n + 1;
//     }
// }

method RotateLeft(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
    ensures a[a.Length -1] == old(a[0])
{
    var n := 0;
    while n != a.Length - 1
        invariant 0 <= n <= a.Length - 1
        invariant forall i :: 0 <= i < n ==> a[i] == old(a[i+1]) 
        invariant a[n] == old(a[0])
        invariant forall i :: n < i <= a.Length-1 ==> a[i] == old(a[i])
    {
        a[n], a[n+1] := a[n+1], a[n];
        n := n + 1; 
    }
}

// Original davinci-003 completion:
// method RotateLeft(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
//     ensures a[a.Length -1] == old(a[0])
// {
//     var n := 0;
//     // loop invariant: forall i :: 0 <= i < n ==> a[i] == old(a[(i+1)])
//     while n != a.Length - 1
//     {
//         a[n], a[n+1] := a[n+1], a[n];
//         n := n + 1; 
//     }
// }

// Fine_tuned davinci-003 completion:
// method RotateLeft1(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)])
//     ensures a[a.Length -1] == old(a[0])
// {
//     var n := 0;
//     while n != a.Length - 1
//         invariant 0 <= n <= a.Length - 1
//         invariant forall i :: 0 <= i < n ==> a[i] == old(a[(i+1)])
//         invariant forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)])
//     {
//         a[n], a[n+1] := a[n+1], a[n];
//         n := n + 1;
//     }
// }

method RotateRight(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
    ensures a[0] == old(a[a.Length-1])
{
    var n := 1;
    while n != a.Length
        invariant 1 <= n <= a.Length
        invariant forall i :: 1 <= i < n ==> a[i] == old(a[i-1]) 
        invariant a[0] == old(a[n-1])
        invariant forall i :: n <= i <= a.Length-1 ==> a[i] == old(a[i])
    {
        a[0], a[n] := a[n], a[0]; n := n + 1;
    } 
}

// Original davinci-003 completion:
// method RotateRight(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
//     ensures a[0] == old(a[a.Length-1])
// {
//     var n := 1;
//     var temp := a[0];
//     while n != a.Length
//     {
//         a[0] := a[n];
//         a[n] := temp;
//         temp := a[0];
//         n := n + 1;
//         // loop invariant:
//         // forall k :: 0 <= k < n ==> a[k] == old(a[k+1])
//     } 
// }

// Fine_tuned davinci-003 completion:
// method RotateRight1(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)])
//     ensures a[0] == old(a[a.Length-1])
// {
//     var n := 1;
//     while n != a.Length
//         invariant 1 <= n <= a.Length
//         invariant forall i :: 1<= i < n ==> a[i] == old(a[(i-1)])
//         invariant forall i :: 1<= i < a.Length ==> a[i] == old(a[i])
//     {
//         a[0], a[n] := a[n], a[0]; n := n + 1;
//     }
// }
