import "magma/TernaryForms.m": Dehomogenization,Homogenization;

SetSeed(1);
SetVerbose("IsGL2Equiv", 0);

_<x> := PolynomialRing(Rationals());
_<x> := PolynomialRing(NumberField(x^2+x+1));
f := x^5 + x;
f := 4*x^6 + 1;
f := x^6 + x^5 + 2*x^3 + 5*x^2 + x + 1;

while true do
    print "Covariant:";
    time _, IsoLst := IsGL2GeometricEquivalent(f, f, 6 : commonfield := true);
    print "Direct:";
    time _, IsoLst := IsGL2GeometricEquivalent(f, f, 6 : commonfield := true, covariant := false);
    //print #IsoLst;
    //print Universe(IsoLst[1]);
end while;

/*
"";
for Iso in IsoLst do
    _f := Homogenization(PolynomialRing(Universe(Iso))!f : degree := 6);
    CoefficientRing(Parent(_f));
    g := TransformForm(_f, Matrix(2, 2, Iso));
    g/_f in Universe(Iso);
end for;
*/
