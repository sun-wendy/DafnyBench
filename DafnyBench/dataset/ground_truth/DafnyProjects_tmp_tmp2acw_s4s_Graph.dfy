// Simple directed graph with vertices of any type T.
class {:autocontracts} Graph<T(==)> {
   var V: set<T>; // vertex-set
   var E: set<(T, T)>; // edge-set

   // Class invariant.
   ghost predicate Valid() {
       // edges must refer to vertices that belong to the vertex-set 
       // and self-loops (edges connecting a vertex to itself) are not allowed 
       forall e :: e in E ==> e.0 in V && e.1 in V && e.0 != e.1
   } 

   // Creates an empty graph.
   constructor ()
     ensures V == {} && E == {}
     {
       V:= {};
       E := {};
     }

   // Adds a new vertex v to this graph.
   method addVertex(v: T)
     requires v !in V
     ensures E == old(E) && V == old(V) + {v}
     {
        V := V + {v};
     }

   // Adds a new edge (u, v) to this graph.
   method addEdge(u: T, v: T)
     requires u in V && v in V && (u, v) !in E && u != v
     ensures V == old(V) && E == old(E) + {(u, v)} 
     {
        E := E + {(u, v)};
     }

   // Obtains the set of vertices adjacent to a given vertex v. 
   function getAdj(v: T): set<T>
     requires v in V
     {
        set e | e in E && e.0 == v :: e.1
     } 

   // Removes a vertex v and all the edges incident on v from the graph.
   method removeVertex(v: T)
     requires v in V
     ensures V == old(V) - {v}
     ensures E == set e | e in old(E) && e.0 != v && e.1 != v 
     {
        V := V - {v};
        E := set e | e in E && e.0 != v && e.1 != v;
     }

    // Collapses a subset C of vertices to a single vertex v (belonging to C).
    // All vertices in C are removed from the graph, except v.  
    // Edges that connect vertices in C are removed from the graph.  
    // In all other edges, vertices belonging to C are replaced by v.
    method collapseVertices(C: set<T>, v: T)
      requires v in C && C <= V 
      ensures V == old(V) - C + {v}
      ensures E == set e | e in old(E) && (e.0 !in C || e.1 !in C) ::
                          (if e.0 in C then v else e.0, if e.1 in C then v else e.1)
  {
        V := V - C + {v};
        E := set e | e in E && (e.0 !in C || e.1 !in C) ::
                          (if e.0 in C then v else e.0, if e.1 in C then v else e.1);
  }    
}

method testGraph() {
    var G := new Graph<int>();
    assert G.E == {} && G.V == {};

    G.addVertex(1);
    G.addVertex(2);
    G.addVertex(3);
    G.addVertex(4);
    assert G.V == {1, 2, 3, 4};

    G.addEdge(1, 2);
    G.addEdge(1, 3);
    G.addEdge(2, 3);
    G.addEdge(4, 1);
    assert G.E == {(1, 2), (1, 3), (2, 3), (4, 1)};

    assert G.getAdj(1) == {2, 3};

    G.collapseVertices({1, 2, 3}, 3);
    assert G.V == {3, 4} && G.E == {(4, 3)};
}

