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


function FindPointOnConic(L : RationalPoint := true, RandomLine := true, Legendre := false, B := 100)
    /* B is the maximal height of the integral coefficients of the intersecting line. */

    K := BaseRing(Parent(L));
    P := ProjectiveSpace(K, 2); x := P.1; y := P.2; z := P.3;
    C := Conic(P, L);

    /* Can we find a rational point on this conic ? */
    if (Type(K) eq FldFin) or (RationalPoint
	and ((Type(K) in {FldRat, FldFin, RngInt}) or
	     (Type(K) eq FldAlg and (
	            Degree(K) eq 1 or IsSimple(K))) or
	     (Type(K) eq FldFunRat and (
		    Type(BaseField(K)) eq FldRat or
		    ISA(Type(BaseField(K)),FldNum) or
		    (IsFinite(BaseField(K)) and Characteristic(BaseField(K)) ne 2 ))) or

	     (ISA(Type(K), FldFunG) and Characteristic(K) ne 2)))
	then
	HasRatPoint, Pt := HasRationalPoint(C);
	if HasRatPoint then
	    vprintf G3Twists, 1 : "Conic has a rational point\n";
	    return Parametrization(C, Place(Pt), Curve(ProjectiveSpace(K, 1)));
	end if;
	vprintf G3Twists, 1 : "Conic has no rational point\n";
    end if;

    /* Since we have no rational point on it, let us construct a quadratic extension that contains one */
    if Legendre then
        LC, LMmap := LegendreModel(C); LL := DefiningPolynomial(LC);
    else
        LC := C; LL := DefiningPolynomial(LC);
    end if;

    if RandomLine then
        D := [-B..B];
        repeat
            c1 := Random(D);
            c2 := Random(D);
            c3 := Random(D);
        until c2 ne 0;
        R<t> := PolynomialRing(K);
        h := hom<Parent(LL) -> R | [R.1, -(c1/c2)*R.1 - 1, 1]>;
        S := ExtensionField < K, t | h(LL) >;
        Pt := [ S | S.1, (-c1/c2)*S.1 - 1, 1];
    else
        a := K ! MonomialCoefficient(LL, x^2); b := K ! MonomialCoefficient(LL, x*z); c := K ! MonomialCoefficient(LL, z^2);
        S := ExtensionField < K, x | a*x^2 + b*x + c >;
        Pt := [ S | S.1, 0, 1];
    end if;

    CS := Conic(ProjectiveSpace(S, 2), L);
    if Legendre then
        Pt := [ Evaluate(p, Pt) : p in DefiningPolynomials(Inverse(LMmap)) ];
    end if;
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

/* Temporary copy: */
function TransformForm(f, T : co := true, contra := false)
    R := Parent(f);
    vars := Matrix([ [ mon ] : mon in MonomialsOfDegree(R, 1) ]);
    if (not co) or contra then
        return Evaluate(f, Eltseq(ChangeRing(Transpose(T)^(-1), R) * vars));
    end if;
    return Evaluate(f, Eltseq(ChangeRing(T, R) * vars));
end function;

function Genus3ConicAndQuartic(JI : models := true, RationalModel := true, Deterministic := false)

    FF := Universe(JI);

    J2, J3, J4, J5, J6, J7, J8, J9, J10 := Explode(JI);

    R := FF!0;

    if Type(FF) eq FldRat and RationalModel eq true then

	Puv := PolynomialRing(FF, 2); u := Puv.1; v := Puv.2;

	R, _, _ := Genus3ConicAndQuarticUV([u, v], JI : models := false);

	if R ne 0 and Degree(R,u)*Degree(R,v) ne 0 then

	    /* Let us find a conic with small discriminant */

	    vprintf G3Twists, 2 :  "Let us minimize the discriminant of the conic to be used, i.e %o\n\n", R;

	    U, V := MinimizeLinearEquationOverRationals(R);

	    vprintf G3Twists, 2 :  "We set :";
	    vprintf G3Twists, 2 :  "  u = %o\n", U;
	    vprintf G3Twists, 2 :  "  v = %o\n", V;

	    R, C, Q := Genus3ConicAndQuarticUV([FF | U, V], JI : models := models);

	    vprintf G3Twists, 2 :  "So that :";
	    vprintf G3Twists, 2 :  "  R = %o\n", R;

	    /* Let us first remove the content of C and Q */
	    ct := LCM([Denominator(c) : c in Coefficients(C)]) /
		  GCD([Numerator(c) : c in Coefficients(C)]);
	    C *:= ct;
	    ct := LCM([Denominator(c) : c in Coefficients(Q)]) /
		GCD([Numerator(c) : c in Coefficients(Q)]);
	    Q *:= ct;

            //vprintf G3Twists, 2 :
            //    "Factorization of conic discriminant before reduction: %o\n",
            //    Factorization(Integers() ! Discriminant(Conic(ProjectiveSpace(Parent(C)), C)));

            vprintf G3Twists, 2 : "Minimal model step...\n";
	    Cphi, phi := MinimalModel(Conic(ProjectiveSpace(Parent(C)), C));
	    C := DefiningPolynomial(Cphi);
	    Q := Evaluate(Q, DefiningPolynomials(phi));
	    ct := GCD([Denominator(c) : c in Coefficients(Q)]) /
		  GCD([Numerator(c) : c in Coefficients(Q)]);
	    Q *:= ct;
	    vprintf G3Twists, 2 :  "Conic %o\n", C;
	    vprintf G3Twists, 2 :  "Quartic %o\n", Q;

            /* This does not seem to be useful in practice: */
            if false then
                /* For some reason the following factorization is necessary first: */
                vprintf G3Twists, 2 : "Reduced Legendre step...\n";
                Fac := Factorization(Integers() ! Discriminant(Conic(ProjectiveSpace(Parent(C)), C)));
                Cphi, phi := ReducedLegendreModel(Conic(ProjectiveSpace(Parent(C)), C));
                C := DefiningPolynomial(Cphi);
                Q := Evaluate(Q, DefiningPolynomials(Inverse(phi)));
                ct := GCD([Denominator(c) : c in Coefficients(Q)]) /
                      GCD([Numerator(c) : c in Coefficients(Q)]);
                Q *:= ct;
                vprintf G3Twists, 2 :  "Conic %o\n", C;
                vprintf G3Twists, 2 :  "Quartic %o\n", Q;

                vprintf G3Twists, 2 : "Further minimal model step...";
                Cphi, phi := MinimalModel(Conic(ProjectiveSpace(Parent(C)), C));
                C := DefiningPolynomial(Cphi);
                Q := Evaluate(Q, DefiningPolynomials(phi));
                ct := GCD([Denominator(c) : c in Coefficients(Q)]) /
                      GCD([Numerator(c) : c in Coefficients(Q)]);
                Q *:= ct;
                vprintf G3Twists, 2 :  "Conic %o\n", C;
                vprintf G3Twists, 2 :  "Quartic %o\n", Q;

                vprintf G3Twists, 2 : "Quartic reduction...";
                Q, T := MinimizeReducePlaneQuartic(Q);
                C := TransformForm(C, T);
                ct := GCD([Denominator(c) : c in Coefficients(C)]) /
                      GCD([Numerator(c) : c in Coefficients(C)]);
                C *:= ct;
                vprintf G3Twists, 2 :  "Conic %o\n", C;
                vprintf G3Twists, 2 :  "Quartic %o\n", Q;
            end if;

	    vprintf G3Twists, 2 :  "Cluster reduction...\n";
            _, T := ReduceMestreConicAndQuartic(C, Q);

	    C := Evaluate(C, T);
            gcd_den := GCD([ Denominator(coeff) : coeff in Coefficients(C) ]);
            gcd_num := GCD([ Numerator(coeff) : coeff in Coefficients(C) ]);
            C *:= (gcd_den/gcd_num);

            Q := Evaluate(Q, T);
            gcd_den := GCD([ Denominator(coeff) : coeff in Coefficients(Q) ]);
            gcd_num := GCD([ Numerator(coeff) : coeff in Coefficients(Q) ]);
            Q *:= (gcd_den/gcd_num);

            vprintf G3Twists, 1 :  "Conic after reduction steps: %o\n", C;
            vprintf G3Twists, 1 :  "Quartic after reduction steps: %o\n", Q;
            vprintf G3Twists, 2 :
                "Factorization of conic discriminant after reduction: %o\n",
                Factorization(Integers() ! Discriminant(Conic(ProjectiveSpace(Parent(C)), C)));
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

	phi := FindPointOnConic(C : RationalPoint := RationalModel, RandomLine := not Deterministic);

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
	    PCx := PolynomialRing(FF); X := PCx.1;
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
