datatype BYTree = BlueLeaf | YellowLeaf | Node(l: BYTree, r: BYTree)

function ReverseColors(t: BYTree): BYTree {
    match t
    case BlueLeaf => YellowLeaf
    case YellowLeaf => BlueLeaf
    case Node (left, right) => Node(ReverseColors(left), ReverseColors(right))
}

lemma {:induction false} ReverseReverseColors(t: BYTree)
ensures  ReverseColors(ReverseColors(t)) == t
{
    if t.BlueLeaf? || t.YellowLeaf? {
    } else {
        calc {
            ReverseColors(ReverseColors(t));
        == // def. Node
            ReverseColors(Node(ReverseColors(t.l), ReverseColors(t.r)));
        == // dist. ReverseColors
            Node(ReverseColors(ReverseColors(t.l)),ReverseColors(ReverseColors(t.r)));
        == { ReverseReverseColors(t.l); }
            Node((t.l), ReverseColors(ReverseColors(t.r)));
        == { ReverseReverseColors(t.r); }
            Node(t.l, t.r);
        == // def. Node
            t;

        }
    }

}