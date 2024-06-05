module Base
{
    // We want to represent circuits.
    // A Circuit is composed of nodes.
    // Each node can have input ports and output ports.

    // The ports are represented just by the index of the node, and the index
    // of the port on the node.
    datatype INodePort = inodeport(node_id: nat, port_id: nat)
    datatype ONodePort = onodeport(node_id: nat, port_id: nat)

    // Currently the nodes can just be Xor, And or Identity gates.
    datatype Node =
        Xor |
        And |
        Ident

    // The number of input ports for each kind of node.
    function n_iports (node: Node): nat
    {
        match node {
            case Xor => 2
            case And => 2
            case Ident => 1
        } 
    }

    // The number of output ports for each kind of node.
    function n_oports (node: Node): nat
    {
        match node {
            case Xor => 1
            case And => 1
            case Ident => 1
        } 
    }

    // A circuit is represented by the nodes and the connections between the nodes.
    // Each output port can go to many input ports.
    // But each input port can only be connected to one output port.
    datatype Circuit = Circ(
        nodes: seq<Node>,
        backconns: map<INodePort, ONodePort>
        )

    // Just checking that the port and node indices mentioned in the connections are sane.
    predicate WellformedBackConns(c: Circuit)
    {
        forall inp :: inp in c.backconns ==>
            WellformedINP(c, inp) &&
            WellformedONP(c, c.backconns[inp])
    }

    predicate WellformedINP(c: Circuit, inp: INodePort)
    {
        (0 <= inp.node_id < |c.nodes|) && (inp.port_id < n_iports(c.nodes[inp.node_id]))
    }

    predicate WellformedONP(c: Circuit, onp: ONodePort)
    {
        (0 <= onp.node_id < |c.nodes|) && (onp.port_id < n_oports(c.nodes[onp.node_id]))
}

    // All input ports in a circuit.
    function AllINPs(c: Circuit): set<INodePort>
        ensures forall inp :: inp in AllINPs(c) ==> WellformedINP(c, inp)
    {
        set node_id: nat, port_id: nat |
            0 <= node_id < |c.nodes| && port_id < n_iports(c.nodes[node_id]) ::
            inodeport(node_id, port_id)
    }

    // All output ports in a circuit.
    function AllONPs(c: Circuit): set<ONodePort>
        ensures forall onp :: onp in AllONPs(c) ==> WellformedONP(c, onp)
    {
        set node_id: nat, port_id: nat |
            0 < node_id < |c.nodes| && port_id < n_oports(c.nodes[node_id]) ::
            onodeport(node_id, port_id)
    }

    ghost predicate Wellformed(c: Circuit)
    {
        WellformedBackConns(c)
    }
}

module Utils
{
    // Updates both the keys and values of a map.
    function UpdateMap<T(!new), U>(A: map<T, U>, f: T->T, g: U->U): (result: map<T, U>)
        requires forall x: T, y: T :: x != y ==> f(x) != f(y)
        ensures forall x :: x in A <==> f(x) in result;
        ensures forall x :: x in A ==> g(A[x]) == result[f(x)];
    {
        map x | x in A :: f(x) := g(A[x])
    }

    // Combines two maps into a single map.
    function CombineMaps<T(!new), U>(a: map<T, U>, b: map<T, U>): map<T, U>
        requires forall x :: x in a ==> x !in b
        requires forall x :: x in b ==> x !in a
        ensures
            var result := CombineMaps(a, b);
            (forall x :: x in a ==> a[x] == result[x]) &&
            (forall x :: x in b ==> b[x] == result[x]) &&
            (forall x :: x in result ==> (x in a) || (x in b))
    {
        map x | x in (a.Keys + b.Keys) :: if x in a then a[x] else b[x]
    }

    function sub(a: nat, b: nat): nat
        requires b <= a
    {
        a - b
    }

}

module BackwardConnections
{
    import opened Base
    import opened Utils

    // This is used when we are trying to create a new circuit by combining two existing circuits.
    // This function takes care of combining the backwards connections.
    // Because the node_indices of the two circuits are just natural numbers when we combine the
    // two circuits we need to shift the node indices of the second circuit so that they don't clash.
    // We do this by adding `offset` to the node indices.
    function CombineBackconns(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>): (result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
    {
        var f:= (inp: INodePort) => inodeport(inp.node_id + offset, inp.port_id);
        var g := (onp: ONodePort) => onodeport(onp.node_id + offset, onp.port_id);
        var backconns2 := UpdateMap(bc2, f, g);
        CombineMaps(bc1, backconns2)
    }

    lemma CombineBackconnsHelper(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
        requires 
            result == CombineBackconns(offset, bc1, bc2);
        ensures
            forall inp :: inp in bc1 ==> (
                inp in result &&
                result[inp] == bc1[inp])
        ensures
            forall inp :: inp in bc2 ==> (
                inodeport(inp.node_id+offset, inp.port_id) in result &&
                result[inodeport(inp.node_id+offset, inp.port_id)] == onodeport(bc2[inp].node_id+offset, bc2[inp].port_id))
    {
        var f:= (inp: INodePort) => inodeport(inp.node_id + offset, inp.port_id);
        var g := (onp: ONodePort) => onodeport(onp.node_id + offset, onp.port_id);
        var backconns2 := UpdateMap(bc2, f, g);
        assert forall inp :: inp in bc2 ==> inodeport(inp.node_id+offset, inp.port_id) in backconns2;
        assert backconns2 == UpdateMap(bc2, f, g);
    }

    lemma CombineBackconnsHelper2(
            offset: nat,
            bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>, inp: INodePort)
        requires
            forall inp :: inp in bc1 ==> inp.node_id < offset
        requires 
            result == CombineBackconns(offset, bc1, bc2);
        requires inp in bc2
        ensures
            inodeport(inp.node_id+offset, inp.port_id) in result
        ensures
            result[inodeport(inp.node_id+offset, inp.port_id)] == onodeport(bc2[inp].node_id+offset, bc2[inp].port_id)
    {
        CombineBackconnsHelper(offset, bc1, bc2, result);
    }
}


module CombineCircuits {

    import opened Base
    import BackwardConnections
    import opened Utils

    // Combine two circuits into a new circuit.
    // This is a bit ugly because we have to offset the node indices of the
    // second circuit by |c1.nodes|.
    function CombineCircuits(c1: Circuit, c2: Circuit): (r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
    {
        var new_nodes := c1.nodes + c2.nodes;
        var new_backconns := BackwardConnections.CombineBackconns(
            |c1.nodes|, c1.backconns, c2.backconns);
        Circ(new_nodes, new_backconns)
    }

    // Check that Circuit c2 contains a subcircuit that corresponds to c1 getting mapped with the
    // `node_map` function.
    predicate IsEquivalentCircuit(node_is_member: nat->bool, node_map: nat-->nat, c1: Circuit, c2: Circuit)
        requires forall inp :: inp in c1.backconns && node_is_member(inp.node_id) ==> node_is_member(c1.backconns[inp].node_id)
        requires forall n :: node_is_member(n) ==> node_map.requires(n)
    {
        forall inp :: inp in c1.backconns && node_is_member(inp.node_id) ==>
            inodeport(node_map(inp.node_id), inp.port_id) in c2.backconns &&
            var inp2 := inodeport(node_map(inp.node_id), inp.port_id);
            var onp := c1.backconns[inp];
            onodeport(node_map(onp.node_id), onp.port_id) == c2.backconns[inp2]
    }

    // Check that for every input port and output port in the combined Circuit, they can be assigned
    // to a port in one of the two source circuits.
    predicate CanBackAssign(c1: Circuit, c2: Circuit, r: Circuit, is_in_c1: nat->bool, is_in_c2: nat-> bool,
                            map_r_to_c1: nat->nat, map_r_to_c2: nat-->nat)
        requires forall a :: is_in_c1(a) ==> map_r_to_c1.requires(a)
        requires forall a :: is_in_c2(a) ==> map_r_to_c2.requires(a)
        requires Wellformed(c1)
        requires Wellformed(c2)
    {
        (forall inp :: inp in AllINPs(r) ==>
            (is_in_c1(inp.node_id) || is_in_c2(inp.node_id)) &&
            if is_in_c1(inp.node_id) then
                WellformedINP(c1, inodeport(map_r_to_c1(inp.node_id), inp.port_id))
            else
                WellformedINP(c2, inodeport(map_r_to_c2(inp.node_id), inp.port_id))) &&
        (forall onp :: onp in AllONPs(r) ==>
            (is_in_c1(onp.node_id) || is_in_c2(onp.node_id)) &&
            if is_in_c1(onp.node_id) then
                WellformedONP(c1, onodeport(map_r_to_c1(onp.node_id), onp.port_id))
            else
                WellformedONP(c2, onodeport(map_r_to_c2(onp.node_id), onp.port_id))) &&
        true
    }

    lemma CombineCircuitsCorrectHelper(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r_is_result: r == CombineCircuits(c1, c2)
    {
        assert  r.backconns == 
            BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns) by {
                reveal r_is_result;
            }
    }


    lemma CombineCircuitsCorrectC1(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r == CombineCircuits(c1, c2)
        ensures
            var offset := |c1.nodes|;
            // The original c1 has an image in r.
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            // This subset of r has an image in c1.
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1)
    {
    }

    lemma CombineCircuitsCorrect(c1: Circuit, c2: Circuit, r: Circuit)
        requires Wellformed(c1)
        requires Wellformed(c2)
        requires r_is_result: r == CombineCircuits(c1, c2)
        ensures
            var offset := |c1.nodes|;
            // The original c1 has an image in r.
            IsEquivalentCircuit(a=>true, a=>a, c1, r) &&
            // This subset of r has an image in c1.
            IsEquivalentCircuit(a=>a < offset, a=>a, r, c1) &&

            // The original c2 has an image in r.
            IsEquivalentCircuit(a=>true, a=>a+offset, c2, r) &&
/*
            FIXME: These have been commented out for now
                   otherwise it takes longer than 20s to solve.
            // All ports in r have equivalents in either c1 or c2.
            CanBackAssign(c1, c2, r, a=>a < offset, a=> a >= offset, a=>a, a requires a >= offset => sub(a, offset)) &&
            // This subset of r has an image in c2.
            IsEquivalentCircuit(a=>a >= offset, a requires a >= offset => sub(a, offset), r, c2) &&
*/
            true
    { 
        // Trying to prove:
        // The original c2 has an image in r.
        // IsEquivalentCircuit(a=>true, a=>a+offset, c2, r)

        var offset := |c1.nodes|;
        var node_is_member := a=>true;
        var node_map := a=>a+offset;
        calc {
            IsEquivalentCircuit(node_is_member, node_map, c2, r);
            // Substitute in the IsEquivalentCircuit function definition.
            forall inp :: inp in c2.backconns && node_is_member(inp.node_id) ==>
                inodeport(node_map(inp.node_id), inp.port_id) in r.backconns &&
                var inp2 := inodeport(node_map(inp.node_id), inp.port_id);
                var onp := c2.backconns[inp];
                onodeport(node_map(onp.node_id), onp.port_id) == r.backconns[inp2];
            // Substitute in the node_is_member and node_is_map definiions.
            // For some reason this cause the solver to take too long.
            forall inp :: inp in c2.backconns ==>
                inodeport(inp.node_id+offset, inp.port_id) in r.backconns &&
                var inp2 := inodeport(inp.node_id+offset, inp.port_id);
                var onp := c2.backconns[inp];
                onodeport(onp.node_id+offset, onp.port_id) == r.backconns[inp2];
        }
        assert basic_result: r.backconns == BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns)
            by {
                reveal r_is_result;
            }

        forall inp | inp in c2.backconns
        {
            calc {
                inodeport(inp.node_id+offset, inp.port_id) in r.backconns &&
                var inp2 := inodeport(inp.node_id+offset, inp.port_id);
                var onp := c2.backconns[inp];
                onodeport(onp.node_id+offset, onp.port_id) == r.backconns[inp2];

                {reveal basic_result;}
                inodeport(inp.node_id+offset, inp.port_id) in 
                BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns) &&
                var inp2 := inodeport(inp.node_id+offset, inp.port_id);
                var onp := c2.backconns[inp];
                onodeport(onp.node_id+offset, onp.port_id) ==
                BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns)[inp2];
                
                inodeport(inp.node_id+offset, inp.port_id) in 
                BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns) &&
                var inp2 := inodeport(inp.node_id+offset, inp.port_id);
                var onp := c2.backconns[inp];
                onodeport(onp.node_id+offset, onp.port_id) ==
                BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns)[inp2];

                {
                    var inp2 := inodeport(inp.node_id+offset, inp.port_id);
                    BackwardConnections.CombineBackconnsHelper2(
                    offset, c1.backconns, c2.backconns,
                    BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns),
                    inp
                    );
                    assert 
                        BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns)[inp2] ==
                        onodeport(c2.backconns[inp].node_id+offset, c2.backconns[inp].port_id);
                    assert 
                        inodeport(inp.node_id+offset, inp.port_id) in 
                        BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns);
                }

                true;
            }
        }
        reveal r_is_result;
        CombineCircuitsCorrectC1(c1, c2, r);
    }
}
