function BlueCount(t: BYTree): nat {
    match t
    case BlueLeaf => 1
    case YellowLeaf => 0
    case Node(left, right) => BlueCount(left) + BlueCount(right) 
}

datatype BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)