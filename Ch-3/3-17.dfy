function F(x: nat, y: nat): int 
decreases - min (x,y)
{
    if 1000 <= x then
        x + y
    else if x % 2 == 0 then
        F(x + 2, y + 1)
    else if x < 6 then
        F(2 * y, y) // This case can only happen when x is odd. So, maybe a cubic function could work.
    else
        F(x - 4, y + 3)
}

function min(x: int, y: int): int
{
    if x >= y then
        y
    else 
        x
}

/* Cases of consideration
    1. x < 6 && x is odd && y = 0
        Will lead to the case x and y = 0 then, both will increase until x exceeds 1000
    2. x is even
        x will increase
    3. x >=6 and odd
        x will eventually become an odd number below 6
*/