datatype BYTree = BlueLeaf | YellowLeaf | Node(l: BYTree, r: BYTree)

function ReverseColors(t: BYTree): BYTree {
    match t
    case BlueLeaf => YellowLeaf
    case YellowLeaf => BlueLeaf
    case Node (left, right) => Node(ReverseColors(left), ReverseColors(right))
}

// Define LeafCount function
function LeafCount (t: BYTree): int {
    match t
    case Node (_,_) => 1 + LeafCount(t.l) + LeafCount(t.r)
    case _ => 1
}

// Prove the ReverseColors function preserves leaf count
lemma {:induction false} ReversePreserve(t: BYTree) 
ensures LeafCount(ReverseColors(t)) == LeafCount(t)
{
    if t.BlueLeaf? || t.YellowLeaf? {
    } else {
        calc {
            LeafCount(ReverseColors(t));
        == // def. Node
            LeafCount(Node(ReverseColors(t.l), ReverseColors(t.r)));
        == // def. LeafCount
            1 + LeafCount(ReverseColors(t.l)) + LeafCount(ReverseColors(t.r));
        == { ReversePreserve(t.l); }
            1 + LeafCount(t.l) + LeafCount(ReverseColors(t.r));
        == { ReversePreserve(t.r); }
            1 + LeafCount(t.l) + LeafCount(t.r);
        == // def. LeafCount
            LeafCount(t);}

    }
}