datatype BYTree = BlueLeaf | YellowLeaf | Node(l: BYTree, r: BYTree)

function ReverseColors(t: BYTree): BYTree {
    match t
    case BlueLeaf => YellowLeaf
    case YellowLeaf => BlueLeaf
    case Node (left, right) => Node(ReverseColors(left), ReverseColors(right))
}

function LeafCount (t: BYTree): int {
    match t
    case Node (_,_) => 1 + LeafCount(t.l) + LeafCount(t.r)
    case _ => 1
}

function BlueCount(t: BYTree): nat {
    match t
    case BlueLeaf => 1
    case YellowLeaf => 0
    case Node(left, right) => BlueCount(left) + BlueCount(right)
}

function Oceanize(t: BYTree): BYTree{
    match t
    case Node(left, right) => Node(Oceanize(left),Oceanize(right))
    case _ => BlueLeaf
}

// Prove a lemma that shows BlueCount(t) <= BlueCount(Oceanize(t))
lemma {:induction false} BlueIncrease(t: BYTree) 
ensures BlueCount(t) <= BlueCount(Oceanize(t))
{
    // assert LeafCount(t) >= BlueCount(t);
    match t 
    case BlueLeaf =>
    case YellowLeaf =>
    case Node(_,_) =>
        calc {
            BlueCount(t) <= BlueCount(Oceanize(t));
        == { ReverseDifference(t); }
            BlueCount(Oceanize(t)) - BlueCount(ReverseColors(t)) <= BlueCount(Oceanize(t));
        == // Add BlueCount(ReverseColors(t)) to both sides
            BlueCount(Oceanize(t)) <= BlueCount(Oceanize(t)) + BlueCount(ReverseColors(t));
        == // Subtract BlueCount(Oceanize(t)) from both sides
            0 <= BlueCount(ReverseColors(t));
        }
}

/* Complete the supporting lemmas below */

lemma {:induction false} ReverseDifference(t: BYTree)
ensures BlueCount(t) == BlueCount(Oceanize(t)) - BlueCount(ReverseColors(t))
{
    match t
    case BlueLeaf =>
    case YellowLeaf =>
    case Node(_,_) => 
        calc {
            BlueCount(Oceanize(t)) - BlueCount(ReverseColors(t));
        == // def. Node
            BlueCount(Oceanize(Node(t.l, t.r))) - BlueCount(ReverseColors(Node(t.l, t.r)));
        == // dist. Oceanize
            BlueCount(Node(Oceanize(t.l), Oceanize(t.r))) - BlueCount(ReverseColors(Node(t.l, t.r)));
        == // dist. ReverseColors
            BlueCount(Node(Oceanize(t.l), Oceanize(t.r))) - BlueCount(Node(ReverseColors(t.l), ReverseColors(t.r)));
        == // def. BlueCount
            (BlueCount(Oceanize(t.l)) + BlueCount(Oceanize(t.r))) - (BlueCount(ReverseColors(t.l)) + BlueCount(ReverseColors(t.r)));
        == // Rearrange
            BlueCount(Oceanize(t.l)) - BlueCount(ReverseColors(t.l)) + BlueCount(Oceanize(t.r)) - BlueCount(ReverseColors(t.r));
        == { ReverseDifference(t.l); }
            BlueCount(t.l) + BlueCount(Oceanize(t.r)) - BlueCount(ReverseColors(t.r));
        == { ReverseDifference(t.r); }
            BlueCount(t.l) + BlueCount(t.r); 
        == // def BlueCount
            BlueCount(t);
        }
}

/* Lemma below is no longer needed */

// lemma {:induction false} BlueOceanTotal(t: BYTree)
// ensures BlueCount(Oceanize(t)) == LeafCount(t)
// {
//     match t
//     case BlueLeaf =>
//     case YellowLeaf =>
//     case Node(_,_) =>
//         calc {
//             BlueCount(Oceanize(t));
//         == { ReverseDifference(t); }
//             BlueCount(t) + BlueCount(ReverseColors(t));
//         ==
//             LeafCount(t);
//         }
// }