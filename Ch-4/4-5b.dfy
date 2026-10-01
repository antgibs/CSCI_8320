datatype BYTree = BlueLeaf 
                | YellowLeaf 
                | Node(left: BYTree, right: BYTree)

predicate HasLeftTree(t: BYTree, u: BYTree){
    if t.Node? then t.left == u
    else false
}