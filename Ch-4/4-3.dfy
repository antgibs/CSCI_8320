datatype BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)

function Oceanize(t: BYTree): BYTree{
    match t
    case Node(left, right) => Node(Oceanize(left),Oceanize(right))
    case _ => BlueLeaf
}