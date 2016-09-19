/* TODO: We restrict to generic case for now */

import "TernaryForms.m": ConjugateForm, ConjugateMatrix, TransformForm;


function GL2ToGL3(U);
    a,b,c,d := Explode(U);
    return Matrix([[a^2, a*b, b^2], [2*a*c, a*d + b*c, 2*b*d], [c^2, c*d, d^2]]);
end function;


function IsomorphismFromB8(b8);

L<s> := BaseRing(Parent(b8));
g := MinimalPolynomial(s);
sigma := hom<L -> L | -Coefficient(g,1) - s>;
test, L := IsGL2GeometricEquivalent(b8, ConjugateForm(sigma, b8), 8 : geometric := false);
return GL2ToGL3(L[1]);

end function;


function NormalizeCocycle(A);

L<s> := BaseRing(A);
g := MinimalPolynomial(s);
sigma := hom<L -> L | -Coefficient(g,1) - s>;
prod := A * ConjugateMatrix(sigma, A);

lambda := prod[1,1];
B := (lambda/Determinant(A)) * A;
return (lambda/Determinant(A)) * A;

end function;


function CoboundaryRandom(A);

L<s> := BaseRing(A);
g := MinimalPolynomial(s);
sigma := hom<L -> L | -Coefficient(g,1) - s>;

B := 1;
D := [-B..B];
while true do
    for i:=1 to 16 do
        B0 := Matrix(BaseRing(A), [ [ Random(D) + Random(D)*s : c in Eltseq(row) ] : row in Rows(A) ]);
        B := B0 + A * ConjugateMatrix(sigma, B0);
        if Rank(B) eq Rank(A) then
            if A * ConjugateMatrix(sigma, B) eq B then
                //print A * ConjugateMatrix(sigma, B) eq B;
                return B;
            end if;
        end if;
    end for;
    B +:= 1;
end while;

end function;


function CoboundaryLinear(A);
// Slightly better, but still not great because the LLL step underperforms.

L<s> := BaseRing(A);
g := MinimalPolynomial(s);
sigma := hom<L -> L | -Coefficient(g,1) - s>;
r := (Coefficient(g,1)/2) + s;

BB := [ Matrix(L, 3, 3, [ KroneckerDelta(i, j) : j in [1..9] ]) : i in [1..9] ]
cat [ Matrix(L, 3, 3, [ r * KroneckerDelta(i, j) : j in [1..9] ]) : i in [1..9] ];
Sigma := DiagonalMatrix(L, [ 1 : i in [1..9] ] cat [ -1 : i in [1..9] ]);
ASplit1 := Matrix(L, [ Eltseq(A * b) : b in BB ]);
ASplit2 := HorizontalJoin(Matrix(L, [ [ (c + sigma(c))/2 : c in Eltseq(row) ] : row in Rows(ASplit1) ]), Matrix(L, [ [ (c - sigma(c))/(2*s) : c in Eltseq(row) ] : row in Rows(ASplit1) ]));
K := Kernel(Sigma * ASplit2 - 1);

if BaseRing(L) eq Rationals() then
    Lat := Lattice(Matrix(Rationals(), [ [ Rationals() ! c : c in Eltseq(K.i) ] : i in [1..Dimension(K)] ]));
    Lat := LLL(Lat);
end if;

B := 1;
D := [-B..B];
while true do
    for i:=1 to 16 do
        //print "boink";
        v := &+[ Random(D) * Lat.i : i in [1..Rank(Lat)] ];
        B := &+[ v[i] * BB[i] : i in [1..#BB] ];
        if Rank(B) eq Rank(A) then
            //print A * ConjugateMatrix(sigma, B) eq B;
            return B;
        end if;
    end for;
    B +:= 1;
end while;

end function;


function Descent(f, b8);

A := NormalizeCocycle(IsomorphismFromB8(b8));
B := CoboundaryLinear(A);
return TransformForm(f, B);

end function;
