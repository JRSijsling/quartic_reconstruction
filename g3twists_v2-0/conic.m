//freeze;

/***
 *  Mini Toolboox for reconstructing genus 3 hyperelliptic curves with the
 *  conic and quartic method.
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
 *  Copyright 2011, R. Lercier & C. Ritzenthaler
 */

import "conic_123.m" : Genus3ConicAndQuartic123;
import "conic_124.m" : Genus3ConicAndQuartic124;
import "conic_157.m" : Genus3ConicAndQuartic157;
import "conic_136.m" : Genus3ConicAndQuartic136;
import "conic_148.m" : Genus3ConicAndQuartic148;
import "conic_129.m" : Genus3ConicAndQuartic129;

import "conic_125.m" : Genus3ConicAndQuartic125;
import "conic_126.m" : Genus3ConicAndQuartic126;
import "conic_128.m" : Genus3ConicAndQuartic128;
import "conic_146.m" : Genus3ConicAndQuartic146;
import "conic_137.m" : Genus3ConicAndQuartic137;
import "conic_247.m" : Genus3ConicAndQuartic247;
import "conic_1210.m" : Genus3ConicAndQuartic1210;
import "conic_1310.m" : Genus3ConicAndQuartic1310;
import "conic_1211.m" : Genus3ConicAndQuartic1211;
import "conic_1411.m" : Genus3ConicAndQuartic1411;
import "conic_1312.m" : Genus3ConicAndQuartic1312;
import "conic_1313.m" : Genus3ConicAndQuartic1313;
import "conic_1612.m" : Genus3ConicAndQuartic1612;

import "conic_uv.m" : Genus3ConicAndQuarticUV;

import "reduction.m" : ReduceMestreConicAndQuartic;

/*
function CheapIntegerSquareFreePart(i : RationalPoint := true)
    if not RationalPoint then
	return i, 1;
    end if;
    Q := Factorization(i: ECMLimit := 10, MPQSLimit := 0);
    _,af := Squarefree(Q);
    a := FactorizationToInteger(af);
    return i div a^2, a;
end function;

function CheapRationalSquareFreePart(r : RationalPoint := true)
    an, bn := CheapIntegerSquareFreePart(Numerator(r): RationalPoint := RationalPoint);
    ad, bd := CheapIntegerSquareFreePart(Denominator(r): RationalPoint := RationalPoint);
    return an*ad, bn/(ad*bd);
end function;

// Find an affine point (x,y,1) on the projective conic L.
function FindPointOnConic(L : RationalPoint := true)
    K := BaseRing(Parent(L));
    UP := PolynomialRing(K : Global := false); u := UP.1;
    if Type(K) eq FldFin then
	repeat
	    x1 := Random(K); x3 := K!1;
	    LL := Evaluate(L, [UP | x1,u,x3]);
	    t, x2 := HasRoot(LL);
	until t;
	return x1,x2;
    elif IsField(K)  then
	P := ProjectiveSpace(K, 2);
	x := P.1; y := P.2; z := P.3;
	C := Conic(P, L);
	if (Type(K) ne FldRat) or (not RationalPoint) or (not HasRationalPoint(C)) then
	    LC,m := LegendreModel(C);
	    LL := DefiningPolynomial(LC);
	    i1 := K!Coefficient(LL,x,2);
	    i2 := K!Coefficient(LL,y,2);
	    i3 := K!Coefficient(LL,z,2);
	    b1, a1 := CheapRationalSquareFreePart(-i3/i1 : RationalPoint := RationalPoint);
	    b2, a2 := CheapRationalSquareFreePart(-i3/i2 : RationalPoint := RationalPoint);
	    if Type(K) eq FldRat and Abs(b1) lt Abs(b2) then
		if RationalPoint then
		    S := QuadraticField(b1); b := S.1;
		else
		    S := ExtensionField<Rationals(), x | x^2-b1>; b := S.1;
		end if;
		Lsol := [a1*b, 0, 1];
	    else
		if RationalPoint then
		    S := QuadraticField(b2); b := S.1;
		else
		    S := ExtensionField<K, x | x^2-b2>; b := S.1;
		end if;
		Lsol := [0, a2*b, 1];
	    end if;
	    sol := [Evaluate(p,Lsol) : p in DefiningPolynomials(Inverse(m))];
	    return sol[1]/sol[3],sol[2]/sol[3];
	else
	    found := false;
	    repeat
		S := Reduction(Random(C));
		if S[3] ne 0 then
		    found := true;
		else
		    pol := Evaluate(L, [UP | S[1],S[2],u]); // pol = c*u*(u-t)
		    if Coefficient(pol, 2) ne 0 then
			s3 := -Coefficient(pol, 1)/Coefficient(pol, 2);
			found := true;
		    end if;
		end if;
	    until found;
	    assert Evaluate(L, Eltseq(S)) eq 0;
	    if S[3] eq 0 then
		if s3 ne 0 then return S[1]/s3, S[2]/s3; end if;
		// There is only one tangent line...
		if S[1] eq 0 then
		    pol := Evaluate(L, [UP | S[1]+u,S[2],u]); // pol = c*u*(u-t)
		else
		    pol := Evaluate(L, [UP | S[1],S[2]+u,u]); // pol = c*u*(u-t)
		end if;
		s3 := -Coefficient(pol, 1)/Coefficient(pol, 2);
		error if s3 eq 0, "Error in FindPointOnConic";
		assert Evaluate(L, [S[1],S[2],s3]) eq 0;
		return S[1]/s3, S[2]/s3;
	    else
		return S[1]/S[3], S[2]/S[3];
	    end if;
	end if;
    else
	error "Algorithm not available for this type of field.\n";
    end if;
end function;

*/

function FindPointOnConic(L : RationalPoint := true)

    K := BaseRing(Parent(L));
    P := ProjectiveSpace(K, 2); x := P.1; y := P.2; z := P.3;
    C := Conic(P, L);

    /* Can we find a rational point on this conic ? */
    if RationalPoint

	and ((Type(K) in {FldRat, FldFin, RngInt}) or

	     (Type(K) eq FldAlg and (
	            Degree(K) eq 1 or IsSimple(K))) or

	     (Type(K) eq FldFunRat and (
		    Type(BaseField(K)) eq FldRat or
		    ISA(Type(BaseField(K)),FldNum) or
		    (IsFinite(BaseField(K)) and Characteristic(BaseField(K)) ne 2 ))) or

	     (ISA(Type(K), FldFunG) and Characteristic(K) ne 2))

	then

	HasRatPoint, Pt := HasRationalPoint(C);

	if HasRatPoint then

	    return Parametrization(C, Place(Pt), Curve(ProjectiveSpace(K, 1)));

	end if;

	vprintf G3Twists, 1 : "Conic has no rational point\n";

    end if;

    /* Since we have no rational point on it, let us construct a quadratic extension that contains one */
    LC, LMmap := LegendreModel(C); LL := DefiningPolynomial(LC);

    a := K ! Coefficient(LL, x, 2); c := K ! Coefficient(LL, z, 2);

    S := ExtensionField < K, x | x^2 + c / a >;

    Pt := [Evaluate(p, [ S | S.1, 0, 1]) : p in DefiningPolynomials(Inverse(LMmap))];

    CS := Conic(ProjectiveSpace(S, 2), L);

    return Parametrization( CS, Place(CS!Pt), Curve(ProjectiveSpace(S, 1)) );

end function;

function MinimizeLinearEquationOverRationals(LE)
    u := Parent(LE).1; v := Parent(LE).2;

    an := Numerator(MonomialCoefficient(LE, u));
    ad := Denominator(MonomialCoefficient(LE, u));

    bn := Numerator(MonomialCoefficient(LE, v));
    bd := Denominator(MonomialCoefficient(LE, v));

    ct := GCD([an*bd, bn*ad, ad*bd]);

    a := (an*bd) div ct;
    b := (bn*ad) div ct;
    c := (ad*bd) div ct;

    _, U, V := ExtendedGreatestCommonDivisor(a, b);

    return U*c, V*c;
end function;

function Genus3ConicAndQuartic(JI : models := true, RationalModel := true)

    FF := Universe(JI);

    J2, J3, J4, J5, J6, J7, J8, J9, J10 := Explode(JI);

    R := FF!0;

    if Type(FF) eq FldRat and RationalModel eq true then

	Puv := PolynomialRing(FF, 2); u := Puv.1; v := Puv.2;

	R, _, _ := Genus3ConicAndQuarticUV([u, v], JI : models := false);

	if R ne 0 and Degree(R,u)*Degree(R,v) ne 0 then

	    /* Let us find a conic with small discriminant */

	    vprintf G3Twists, 1 :  "Let us minimize the discriminant of the conic to be used, i.e %o\n\n", R;

	    U, V := MinimizeLinearEquationOverRationals(R);

	    vprintf G3Twists, 1 :  "We set :";
	    vprintf G3Twists, 1 :  "  u = %o\n", U;
	    vprintf G3Twists, 1 :  "  v = %o\n", V;

	    R, C, Q := Genus3ConicAndQuarticUV([FF | U, V], JI : models := models);

	    vprintf G3Twists, 1 :  "So that :";
	    vprintf G3Twists, 1 :  "  R = %o\n", R;

	    /* Let us first remove the content of C */
	    ct := GCD([Denominator(c) : c in Coefficients(C)]) /
		  GCD([Numerator(c) : c in Coefficients(C)]);
	    C *:= ct;
	    
	    /* This done, let us minimize C and Q */

	    
	    Cphi, phi := MinimalModel(Conic(ProjectiveSpace(Parent(C)), C));
	    C := DefiningPolynomial(Cphi);
	    vprintf G3Twists, 1 :  "Once minimized, we get the conic %o\n", C;

	    ct := GCD([Denominator(c) : c in Coefficients(Q)]) /
		GCD([Numerator(c) : c in Coefficients(Q)]);
	    Q *:= ct;

	    Q := Evaluate(Q, DefiningPolynomials(phi));


	    ct := GCD([Denominator(c) : c in Coefficients(Q)]) /
		  GCD([Numerator(c) : c in Coefficients(Q)]);
	    Q *:= ct;

	    vprintf G3Twists, 1 :  "And then, the quartic is %o\n", Q;

            _, T := ReduceMestreConicAndQuartic(C, Q);

	    C := Evaluate(C, T);
            gcd_den := GCD([ Denominator(coeff) : coeff in Coefficients(C) ]);
            gcd_num := GCD([ Numerator(coeff) : coeff in Coefficients(C) ]);
            C *:= (gcd_den/gcd_num);
	    vprintf G3Twists, 1 :  "Using cluster reduction, we get the conic %o\n", C;

            Q := Evaluate(Q, T);
            gcd_den := GCD([ Denominator(coeff) : coeff in Coefficients(Q) ]);
            gcd_num := GCD([ Numerator(coeff) : coeff in Coefficients(Q) ]);
            Q *:= (gcd_den/gcd_num);
	    vprintf G3Twists, 1 :  "And then, the quartic is %o\n", Q;

	else
	    R := FF!0;
	end if;
    end if;

    /* Considering conics in turn */
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic123(JI : models := models); end if;

    if R eq 0 then R, C, Q := Genus3ConicAndQuartic124(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic157(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic136(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic148(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic129(JI : models := models); end if;

    if R eq 0 then R, C, Q := Genus3ConicAndQuartic125(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic126(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic128(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic146(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic137(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic247(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1210(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1310(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1211(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1411(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1312(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1313(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic1612(JI : models := models); end if;

    /* No non-degenrate conic found, return immediatly */
    if R eq 0 then return false; end if;

    /* Computing conic and quartic */
    if models then

/*
	    xi, eta := FindPointOnConic(C : RationalPoint := RationalModel);

	    QF := Parent(eta);

	    if QF ne FF then
		vprintf G3Twists, 1 : "Conic has no rational point\n";
	    end if;
	    P3 := PolynomialRing(QF, 3); x1 := P3.1; x2 := P3.2; x3 := P3.3;

	    // "pt is "; [xi, eta, 1];
	    // Evaluate(C, [xi, eta, 1]);

	    pol := Evaluate(C,[xi + x2*x1, eta + x1,1]);


	    a := Coefficient(pol,x1,2);
	    b := Coefficient(pol,x1,1);
	    // "param is", [xi*a-x2*b,a*eta-b,a];
	    return UnivariatePolynomial(Evaluate(Q,[xi*a-x2*b,a*eta-b,a]));

*/

	phi := FindPointOnConic(C : RationalPoint := RationalModel);

	f := Evaluate(Q, DefiningPolynomials(phi));

	return UnivariatePolynomial(Evaluate(f, Parent(f).2, 1));


    end if;

    return true;

end function;

function Genus3ConicAndQuarticForC4(JI : models := true)

    FF := Universe(JI);
    J2, J3, J4, J5, J6, J7, J8, J9, J10 := Explode(JI);

    /* Considering conics in turn */
    R, C, Q := Genus3ConicAndQuartic123(JI : models := models);
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic157(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic129(JI : models := models); end if;

    if R eq 0 then
	R, C, Q := Genus3ConicAndQuartic136(JI : models := models);
	if R ne 0 then
	    PC := Parent(C);  x1 := PC.1; x2 := PC.2; x3 := PC.3;
	    C := Evaluate(C, [x1, x3, x2]); Q := Evaluate(Q, [x1, x3, x2]);
	end if;
    end if;

    /* Usefull for instance for [ 1, 0, 1, 0, 3, 0, 43, 0, 18 ] in GF(47^2) */
    if R eq 0 then R, C, Q := Genus3ConicAndQuartic124(JI : models := models); end if;

    /* No non-degenrate conic found, return immediatly (should not happen) */
    if R eq 0 then
	vprintf G3Twists, 1 : "ARGH, no non-degenerate conic found in a C4 case (this should not happen) \n";
	return false;
    end if;

    /* Computing conic and quartic */
    if models then

	PC := Parent(C);  x1 := PC.1; x2 := PC.2; x3 := PC.3;

	/* If no sparse conic or quartic found,
           return immediatly (this should not happen) */
	Cc, Cm := CoefficientsAndMonomials(C);
	if (Seqset(Cm) meet {x1^2, x2^2, x3^2, x1*x3}) ne Seqset(Cm) then
	    vprintf G3Twists, 1 : "ARGH, no sparse conic found in a C4 case (this should not happen)\n";
	    return false;
	end if;

	Qc, Qm := CoefficientsAndMonomials(Q);
	if (Seqset(Qm) meet {x2*x1^3, x2*x3^3, x2^3*x1, x2*x1^2*x3, x2^3*x3, x2*x1*x3^2}) ne Seqset(Qm) then
	    vprintf G3Twists, 1 : "ARGH, no sparse quartic found in a C4 case (this should not happen)\n";
	    return false;
	end if;

	if Index(Cm, x1^2) eq 0 then c11 := FF!0; else	c11 := Cc[Index(Cm, x1^2)]; end if;
	if Index(Cm, x2^2) eq 0 then c22 := FF!0; else c22 := Cc[Index(Cm, x2^2)];  end if; //c2 = 0 is excluded
	if Index(Cm, x3^2) eq 0 then c33 := FF!0; else c33 := Cc[Index(Cm, x3^2)];  end if;
	if Index(Cm, x1*x3) eq 0 then c13 := FF!0; else c13 := Cc[Index(Cm, x1*x3)]; end if;
	/* "c11 := ", c11, ";"; "c13 := ", c13, ";"; "c22 := ", c22, ";"; "c33 := ", c33, ";"; ""; */

	if c11 eq 0 then
	    /* "HUM, c11 = 0..."; */
	    xi := -c33/c13; eta := 0;
	    QF := FF;
	else
	    PCx := PolynomialRing(PC); X := PCx.1;
	    QF := quo<PCx | X^2+(c11*c33-1/4*c13^2)/c11/c22>; a := QF.1;
	    xi := -1/2*c13/c11; eta := a;
	end if;
	/* "pt is "; [xi, eta, 1]; */
	/* "Conic evaluated at this point is", Evaluate(C, [xi, eta, 1]); */

	P3 := PolynomialRing(QF, 3); x1 := P3.1; x2 := P3.2; x3 := P3.3;

	pol := Evaluate(C,[xi + x2*x1, eta + x1,1]);
	/* ""; "pol is", pol; */

	A := Coefficient(pol,x1,2);
	B := Coefficient(pol,x1,1);
	/* "param is", [xi*A-x2*B,A*eta-B,A]; */
	f := UnivariatePolynomial(Evaluate(Q,[xi*A-x2*B,A*eta-B,A]));

	if c11 eq 0 then return f; end if;

	F := [Eltseq(c) : c in Eltseq(Evaluate(f, a*Parent(f).1))];
	if Seqset([F[1+i, 1] : i in [0..Degree(f)] | #F[1+i] ne 0]) ne {0} then
	    vprintf G3Twists, 1 : "ARGH, no rational model found in a C4 case (this should not happen)\n";
	end if;

	FFx := PolynomialRing(FF); x := FFx.1;
	fr :=  &+[(FF!F[1+i, 2])*x^(i) : i in [0..Degree(f)] | #F[1+i] ne 0];

	return fr;
    end if;

    return true;

end function;
