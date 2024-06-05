datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

predicate BinarySearchTree(tree: Tree)
  decreases tree
{
  match tree
  case Empty => true
  case Node(_,_,_) =>
    (tree.left == Empty || tree.left.value < tree.value)
    && (tree.right == Empty || tree.right.value > tree.value)
    && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
    && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}

predicate maxValue(tree: Tree, max: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}

predicate minValue(tree: Tree, min: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}

method GetMin(tree: Tree) returns (res: int)
{
  match tree {
    case Empty => res := 0;
    case Node (Empty, value, Empty) => res := tree.value;
    case Node (Empty, value, right) => res := tree.value;
    case Node (left, value, right) =>
      var minval := tree.value;
      minval := GetMin(tree.left);
      var tmp := Node(tree.left, minval, tree.right);
      res := tmp.value;
  }
}

method GetMax(tree: Tree) returns (res: int){
  match tree {
    case Empty => res := 0;
    case Node (Empty, value, Empty) => res := tree.value;
    case Node (left, value, Empty) => res := tree.value;
    case Node (left, value, right) =>
      var minval := tree.value;
      minval := GetMax(tree.right);
      var tmp := Node(tree.left, minval, tree.right);
      res := tmp.value;
  }
}

method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures BinarySearchTree(res)
{
  res := insertRecursion(tree, value);
}

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  match tree {
    case Empty => res := Node(Empty, value, Empty);
    case Node(_,_,_) =>
      var temp: Tree;
      if(value == tree.value) {
        return tree;
      }
      if(value < tree.value){
        temp := insertRecursion(tree.left, value);
        res := Node(temp, tree.value, tree.right);
      }else if (value > tree.value){
        temp := insertRecursion(tree.right, value);
        res := Node(tree.left, tree.value, temp);
      }
  }
}

method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  //ensures BinarySearchTree(res)
  //ensures res != Empty ==> BinarySearchTree(res)
{
  match tree {
    case Empty => return tree;
    case Node(_,_ ,_) =>
      var temp: Tree;
      if (value < tree.value){
        temp := delete(tree.left, value);
        res := Node(temp, tree.value, tree.right);
      } else if (value > tree.value){
        temp := delete(tree.right, value);
        res := Node(tree.left, tree.value, temp);
      } else {
        if (tree.left == Empty){
          return tree.right;
        } else if (tree.right == Empty) {
          return tree.left;
        }
        var minVal := GetMin(tree.right);
        temp := delete(tree.right, minVal);
        res := Node(tree.left, minVal, temp);
        //assert BinarySearchTree(res);
      }
  }
}

method Inorder(tree: Tree)
{
  match tree {
    case Empty =>
    case Node(left, value, right) =>
      Inorder(tree.left);
      print tree.value, ", ";
      Inorder(tree.right);
  }
}

method Postorder(tree: Tree)
{
  match tree {
    case Empty =>
    case Node(left, value, right) =>
      Postorder(tree.left);
      Postorder(tree.right);
      print tree.value, ", ";
  }
}

method Main() {
  var tree := insert(Empty, 3);
  var u := insert(tree, 2);

  u := insert(u, 7);
  u := insert(u, 6);
  u := insert(u, 9);


  print "This is Inorder: ";
  Inorder(u);
  print "\n";
  //u := delete (u, 1);

  print "This is Postorder: ";
  Postorder(u);
  print "\n";

  print "tree before delete: ", u, "\n";

  u := delete(u, 7);
  print "tree after delete: ", u, "\n";

  print "This is Inorder: ";
  Inorder(u);

  print "\n";
  print "This is Postorder: ";
  Postorder(u);

  // var res := GetMin(u);
  // var max := GetMax(u);
  // print "this is max: ", max;
  //print "this is res: ", res;

  //print u;
}
