// Exercise 6.6
function F(x: int, y: int): int

const L: int
const R: int

lemma LeftUnit(x:int)
ensures F(L, x) == x

lemma RightUnit(x: int)
ensures F(x, R) == x

lemma LIsR(x: int)
ensures L == R
{
    calc
    {
        L;
        == { RightUnit(L);}
        F(L, R);
        == { LeftUnit(R);}
        R;
    }
}