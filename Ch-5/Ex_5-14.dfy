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

// Prove a lemma that shows BluCount(t) <= BlueCount(Oceanize(t))
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
        == // def. Node
            BlueCount(Node(t.l, t.r)) <= BlueCount(Oceanize(Node(t.l, t.r)));
        == // def. BlueCount
            BlueCount(t.l) + BlueCount(t.r) <= BlueCount(Oceanize(t.l)) + BlueCount(Oceanize(t.r));
        == // BlueCount(t) = BlueCount(Oceanize(t)) - BlueCount(ReverseColors(t))
            (BlueCount(Oceanize(t.l)) - BlueCount(ReverseColors(t.l))) + (BlueCount(Oceanize(t.r)) - BlueCount(ReverseColors(t.r))) <=  BlueCount(Oceanize(t.l)) + BlueCount(Oceanize(t.r));
        == //  BlueCount(Oceanize(t)) = Leafcount(Oceanize(t))
            BlueCount(t.l) + BlueCount(t.r) <=  LeafCount(Oceanize(t.l)) + LeafCount(t.r);
        }
}

/* Complete the supporting lemmas below */

lemma {:induction false} ReverseDifference(t: BYTree)
ensures BlueCount(t) == BlueCount(Oceanize(t)) - BlueCount(ReverseColors(t))
{}

lemma {:induction false} BlueOceanTotal(t: BYTree)
ensures BlueCount(Oceanize(t)) == LeafCount(t)
{
    match t
    case BlueLeaf =>
    case YellowLeaf =>
    case Node(_,_) =>
        calc {
            BlueCount(Oceanize(t));
        == 

        ==
            LeafCount(t);
        }
}