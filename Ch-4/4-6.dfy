datatype Color = Blue | Yellow | Green | Red

datatype ColoredTree = Leaf(c: Color)
                     | Node(left: ColoredTree, right: ColoredTree)

predicate IsSwedishColoredTree(t: ColoredTree){
    if t.Node? then IsSwedishColoredTree(t.left) && IsSwedishColoredTree(t.right)
    else IsSwedishFlagColor(t.c)
}

predicate IsSwedishFlagColor(c: Color){
    c.Blue? || c.Yellow?
}