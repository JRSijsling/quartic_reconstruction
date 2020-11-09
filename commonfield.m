import "magma/TernaryForms.m": Dehomogenization,Homogenization;

SetVerbose("IsGL2Equiv", 2);
_<x> := PolynomialRing(Rationals());
//_<x> := PolynomialRing(NumberField(x^2+x+1));
f1 := x^5 + x;
f2 := 4*x^6 + 1;
//f2 := x^6 + x^5 + 2*x^3 + 5*x^2 + x + 1;

_, IsoLst1 := IsGL2GeometricEquivalent(f1, f1, 6 : commonfield := true);
print #IsoLst1;
print IsoLst1;
//print { Universe(E) : E in IsoLst1 };
//print { DefiningPolynomial(Universe(E)) : E in IsoLst1 };

/*
_, IsoLst2 := IsGL2GeometricEquivalent(f2, f2, 6 : commonfield := true);
//{ DefiningPolynomial(Universe(E)) : E in IsoLst2 };

"";
for Iso in IsoLst1 do
    _f1 := Homogenization(PolynomialRing(Universe(Iso))!f1 : degree := 6);
    CoefficientRing(Parent(_f1));
    g1 := TransformForm(_f1, Matrix(2, 2, Iso));
    g1/_f1 in Universe(Iso);
end for;

"";
for Iso in IsoLst2 do
    _f2 := Homogenization(PolynomialRing(Universe(Iso))!f2 : degree := 6);
    g2 := TransformForm(_f2, Matrix(2, 2, Iso));
    g2/_f2 in Universe(Iso);
end for;
*/
