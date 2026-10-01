datatype BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)

function ReverseColors(t: BYTree): BYTree {
    match t
    case BlueLeaf => YellowLeaf
    case YellowLeaf => BlueLeaf
    case Node (left, right) => Node(ReverseColors(left), ReverseColors(right))
}