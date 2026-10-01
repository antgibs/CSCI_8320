datatype BYTree = BlueLeaf 
                | YellowLeaf 
                | Node(left: BYTree, right: BYTree)

predicate HasLeftTree(t: BYTree, u: BYTree){
    match t
    case Node(left, right) => u == left
    case _ => false
}