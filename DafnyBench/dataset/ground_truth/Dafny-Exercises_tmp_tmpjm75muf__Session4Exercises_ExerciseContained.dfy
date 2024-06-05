


predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}


method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]//exists j :: 0 <= j < m && v[k] == w[j]
{
	var i:=0;
	var j:=0;
	while(i<n && j<m && (v[i] >= w[j])) //&& b)
	invariant 0<=i<=n
	invariant 0<=j<=m
	invariant strictSorted(v[..])
	invariant strictSorted(w[..])
	invariant forall k::0<=k<i ==> v[k] in w[..j] 
	invariant i<n  ==> !(v[i] in w[..j])
	decreases w.Length-j
	decreases v.Length-i
	{	
		if(v[i] == w[j]){
			i:=i+1;
		}
		j:=j+1;
		
	}
	assert i<n ==> !(v[i] in w[..m]);
	b := i==n;
	
}


