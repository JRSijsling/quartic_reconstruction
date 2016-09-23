/***
 *  Descent functionality for plane quartics.
 *
 *  Distributed under the terms of the GNU Lesser General Public License (L-GPL)
 *                  http://www.gnu.org/licenses/
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation; either version 2.1 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 *  Copyright:
 *  2004 M. Girard, C. Ritzenthaler
 *  2006 D. Kohel
 *  2016 R. Lercier, C. Ritzenthaler & J.R. Sijsling
 */

/* TODO: We restrict to generic case for now */

import "TernaryForms.m": ConjugateForm, ConjugateMatrix, TransformForm;

declare verbose Descent, 1;


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
return B;

end function;


function CoboundaryRandom(A : SmallCoboundary := true);

L<s> := BaseRing(A);
g := MinimalPolynomial(s);
sigma := hom<L -> L | -Coefficient(g,1) - s>;

counter := 0;
Bound := 1;
ECMLimit := 5000;
D := [-Bound..Bound];
while true do
    for i:=1 to (Bound + 1)^3 do
        B0 := Matrix(BaseRing(A), [ [ Random(D) + Random(D)*s : c in Eltseq(row) ] : row in Rows(A) ]);
        B := B0 + A * ConjugateMatrix(sigma, B0);
        if Rank(B) eq Rank(A) then
            if not SmallCoboundary then
                return B, [];
            else
                nm := Norm(Determinant(B));
                num := Abs(Numerator(nm));
                den := Abs(Denominator(nm));
                vprint Reconstruction : "Checking whether the coboundary is small...";
                Fac_num := Factorization(num : MPQSLimit := 0, ECMLimit := ECMLimit);
                Fac_den := Factorization(den : MPQSLimit := 0, ECMLimit := ECMLimit);
                test := (FactorizationToInteger(Fac_num) eq num) and (FactorizationToInteger(Fac_den) eq den);
                if test then
                    bp := Sort([ fac[1] : fac in Fac_num ] cat [ fac[1] : fac in Fac_den ]);
                    vprint Reconstruction : "Primes in coboundary:";
                    vprint Reconstruction : bp;
                    return B, bp;
                end if;
            end if;
        end if;
    end for;
    ECMLimit +:= 1000;
    counter +:= 1;
    if counter mod 4 eq 0 then
        Bound +:= 1;
    end if;
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
ASplit2 := HorizontalJoin(Matrix(L, [ [ (c + sigma(c))/2 : c in Eltseq(row) ] : row in Rows(ASplit1) ]), Matrix(L, [ [ (c - sigma(c))/(2*r) : c in Eltseq(row) ] : row in Rows(ASplit1) ]));
K := Kernel(Sigma * ASplit2 - 1);

if BaseRing(L) eq Rationals() then
    Lat := Lattice(Matrix(Rationals(), [ [ Rationals() ! c : c in Eltseq(K.i) ] : i in [1..Dimension(K)] ]));
    Lat := LLL(Lat);
end if;

B := 1;
D := [-B..B];
while true do
    for i:=1 to 16 do
        v := &+[ Random(D) * Lat.i : i in [1..Rank(Lat)] ];
        B := &+[ v[i] * BB[i] : i in [1..#BB] ];
        if Rank(B) eq Rank(A) then
            //print "Cocycle works?";
            //print A * ConjugateMatrix(sigma, B) eq B;
            return B, [];
        end if;
    end for;
    B +:= 1;
end while;

end function;


function Descent(f, b8 : RandomCoboundary := false, SmallCoboundary := true);

A := NormalizeCocycle(IsomorphismFromB8(b8));
if not RandomCoboundary then
    B, bp := CoboundaryLinear(A);
else
    B, bp := CoboundaryRandom(A : SmallCoboundary := SmallCoboundary);
end if;
f0 := TransformForm(f, B);
return f0 / Coefficients(f0)[1], bp;

end function;
