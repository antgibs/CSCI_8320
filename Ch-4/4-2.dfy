method TestReverseColors() {
    var a := Node(BlueLeaf, Node(BlueLeaf, YellowLeaf));
    var b := Node(YellowLeaf, Node(YellowLeaf, BlueLeaf));
    assert ReverseColors(a) == b;
    assert ReverseColors(b) == a;
    assert ReverseColors(ReverseColors(a)) == a; // Sample Test 1: Reverse of Reverse = Identity
    assert ReverseColors(Node (a,b)) == Node(b,a); // Sample Test 2: Reverse of (a,b) tree = (b,a) tree
    assert ReverseColors(Node (BlueLeaf, b)) == Node(YellowLeaf, a); // Sample Test 3: Reverse colors, not mirror entire tree
    assert ReverseColors(Node(YellowLeaf, a)) == Node(a, YellowLeaf); // Failed Test: Expecting to swap position of the tree's two branches 
}

datatype BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)

function ReverseColors(t: BYTree): BYTree {
    match t
    case BlueLeaf => YellowLeaf
    case YellowLeaf => BlueLeaf
    case Node (left, right) => Node(ReverseColors(left), ReverseColors(right))
}