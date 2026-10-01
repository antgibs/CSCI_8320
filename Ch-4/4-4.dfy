datatype BYTree = BlueLeaf 
                | YellowLeaf 
                | Node(left: BYTree, right: BYTree)

function LeftDepth(t: BYTree): int{
    
    if t.Node? then 1 + LeftDepth(t.left)
    else 0
}