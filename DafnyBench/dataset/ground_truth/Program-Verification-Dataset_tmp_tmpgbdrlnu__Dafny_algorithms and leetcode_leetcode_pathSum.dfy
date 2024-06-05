//https://leetcode.com/problems/path-sum
/**
function hasPathSum(root: TreeNode | null, targetSum: number): boolean {
    if(root == null) {
        return false;
    }
    if(root.val-targetSum == 0 && root.left == null && root.right == null) {
        return true;
    }
    return hasPathSum(root.left, targetSum-root.val) || hasPathSum(root.right, targetSum-root.val);
};
 */

datatype TreeNode = Nil | Cons(val: nat, left: TreeNode, right: TreeNode)

function TreeSeq(root: TreeNode): seq<TreeNode> {
    match root {
        case Nil => [Nil]
        case Cons(val, left, right) => [root]+TreeSeq(left)+TreeSeq(right)
    }
}

function TreeSet(root: TreeNode): set<TreeNode> {
    match root {
        case Nil => {Nil}
        case Cons(val, left, right) => TreeSet(left)+{root}+TreeSet(right)
    }
}

predicate isPath(paths: seq<TreeNode>, root: TreeNode) {
    if |paths| == 0 then false else match paths[0] {
        case Nil => false
        case Cons(val, left, right) => if |paths| == 1 then root == paths[0] else root == paths[0] && (isPath(paths[1..], left) || isPath(paths[1..], right))
    }
}

function pathSum(paths: seq<TreeNode>): nat {
    if |paths| == 0 then 0 else match paths[0] {
        case Nil => 0
        case Cons(val, left, right) => val + pathSum(paths[1..])
    }
}

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
    if root == Nil {
        return false;
    }

    if(root.val - targetSum == 0 && root.left == Nil && root.right == Nil) {
        assert isPath([root], root) && pathSum([root]) == targetSum;
        return true;
    }
    var leftPath := hasPathSum(root.left, targetSum-root.val);
    var rightPath := hasPathSum(root.right, targetSum-root.val);

    if leftPath {
        ghost var p: seq<TreeNode> :| isPath(p, root.left) && pathSum(p) == targetSum-root.val;
        assert isPath([root]+p, root) && pathSum([root]+p) == targetSum;
    }
    if rightPath {
        ghost var p: seq<TreeNode> :| isPath(p, root.right) && pathSum(p) == targetSum-root.val;
        assert isPath([root]+p, root) && pathSum([root]+p) == targetSum;
    }
    return leftPath || rightPath;
}

method Test() {
    var c := Cons(3, Nil, Nil);
    var b := Cons(2, c, Nil);
    var a := Cons(1, b, Nil);
    assert isPath([a], a);
    assert a.left == b;
    assert isPath([a,b], a);
    assert isPath([a,b,c], a);
}



