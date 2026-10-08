datatype BYTree = BlueLeaf | YellowLeaf | Node(l: BYTree, r: BYTree)

function Oceanize(t: BYTree): BYTree{
    match t
    case Node(left, right) => Node(Oceanize(left),Oceanize(right))
    case _ => BlueLeaf
}

// Prove that Oceanize is idempotent
lemma {:induction false} OceanizeIdempotence(t:BYTree)
ensures Oceanize(Oceanize(t)) == Oceanize(t) 
{
    match t
    case BlueLeaf =>
    case YellowLeaf =>
    case Node (_,_) =>
        calc {
            Oceanize(Oceanize(t));
        == // def. Node
            Oceanize(Node(Oceanize(t.l), Oceanize(t.r)));
        == // dist. Oceanize
            Node(Oceanize(Oceanize(t.l)), Oceanize(Oceanize(t.r)));
        == { OceanizeIdempotence(t.l); }
            Node(Oceanize(t.l), Oceanize(Oceanize(t.r)));
        == { OceanizeIdempotence(t.r); }
            Node(Oceanize(t.l), Oceanize(t.r));
        == // dist. Oceanize
            Oceanize(Node(t.l, t.r));
        == // def. Node
            Oceanize(t);
        }
}