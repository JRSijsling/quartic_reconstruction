/* Replace the last function in magma/package/Geometry/SrfDP/ by this: */

intrinsic MinimizeReducePlaneQuartic(f :: RngMPolElt) -> RngMPolElt, Mtrx
{Minimization and reduction of a plane quartic curve with integral coefficients.
 Returns an isomorphic quartic with small coefficients, and the transformation matrix.}

 r := Rank(Parent(f));
 require r eq 3: "Polynomial in 3 variables expected.";
 type := Type(BaseRing(Parent(f)));
 integral := type eq RngInt;
 if type eq FldRat then
  integral, f := IsCoercible(PolynomialRing(Integers(),r), f*Denominator(f));
 end if;
 require integral: "Polynomial over the integers or rationals expected.";

 require IsSmoothHyperSurface(f) : "Curve is singular.";
 require (Degree(f) eq 4) and IsHomogeneous(f) : "Homogeneous polynomial of degree 4 expected.";

 subs := [Parent(f).i : i in [1..3]];
 res := f div GCD(Coefficients(f));
 for p in [2,3,5] do
  vprintf PlaneQuartic,1: "Local minimization for p = %o\n",p;
  repeat
   res,subs_n := LocalMinimizationStepPlaneQuartic(res,p);
   subs := [Evaluate(a,subs_n) : a in subs];
  until  subs_n eq [Parent(f).i : i in [1..3]];
 end for;
 vprintf PlaneQuartic,1: "Computing bad primes.\n";
 bp := ImproveablePrimes(res);
 vprintf PlaneQuartic, 1:"Bad primes %o.\n",bp;
 for p in bp do
  vprintf PlaneQuartic,1: "Local minimization for p = %o\n",p;
  repeat
   res,subs_n := LocalMinimizationStepPlaneQuartic(res,p);
   subs := [Evaluate(a,subs_n) : a in subs];
  until  subs_n eq [Parent(f).i : i in [1..3]];
 end for;

/* Simplify Transformation obtained by the minimization algorithm using LLL */
 Lat := LLL(Matrix([[MonomialCoefficient(subs[j],Parent(f).i) : j in [1..#subs]] : i in [1..Rank(Parent(f))]]));
 Lat := Transpose(Lat);
 res := f^Lat;
 res := res div GCD(Coefficients(res));

/* Final reduction step */
 res, Trr := ReducePlaneCurve(res);

 return res, Lat*Trr;
end intrinsic;
