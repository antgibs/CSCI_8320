// Exercise 6.6
function F(x: int, y: int): int

const L: int
const R: int

lemma LeftZero(x:int)
ensures F(L, x) == L

lemma RightZero(x: int)
ensures F(x, R) == R

lemma LIsRZeroElem(x: int)
ensures L == R
{
    calc
    {
        L;
        == { LeftZero(R); } // Show that L = F(L, R)
        F(L, R);
        == {RightZero(L);} // Show that F(L, R) = R
        R;
    }
}