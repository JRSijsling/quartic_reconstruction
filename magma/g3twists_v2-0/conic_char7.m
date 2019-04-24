//freeze;

/***
 *  Mini Toolboox for reconstructing genus 3 hyperelliptic curves with the
 *  conic and quartic method in characteristic 7.
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
 *  Copyright 2014, R. Basson & R. Lercier & C. Ritzenthaler
 */


import "conic_char7_5671.m" : Genus3Char7ConicAndQuartic5671;
import "conic_char7_5693.m" : Genus3Char7ConicAndQuartic5693;
import "conic_char7_582113.m" : Genus3Char7ConicAndQuartic582113;
import "conic_char7_5672.m" : Genus3Char7ConicAndQuartic5672;
import "conic_char7_5682.m" : Genus3Char7ConicAndQuartic5682;
import "conic_char7_5692.m" : Genus3Char7ConicAndQuartic5692;
import "conic_char7_57172.m" : Genus3Char7ConicAndQuartic57172;
import "conic_char7_57281.m" : Genus3Char7ConicAndQuartic57281;
import "conic_char7_57282.m" : Genus3Char7ConicAndQuartic57282;
import "conic_char7_57292.m" : Genus3Char7ConicAndQuartic57292;
import "conic_char7_57293.m" : Genus3Char7ConicAndQuartic57293;
import "conic_char7_59293.m" : Genus3Char7ConicAndQuartic59293;
import "conic_char7_67281.m" : Genus3Char7ConicAndQuartic67281;
import "conic_char7_67282.m" : Genus3Char7ConicAndQuartic67282;
import "conic_char7_572113.m" : Genus3Char7ConicAndQuartic572113;
import "conic_char7_593121.m" : Genus3Char7ConicAndQuartic593121;
import "conic_char7_717281.m" : Genus3Char7ConicAndQuartic717281;
import "conic_char7_728182.m" : Genus3Char7ConicAndQuartic728182;
import "conic_char7_728191.m" : Genus3Char7ConicAndQuartic728191;
import "conic_char7_729193.m" : Genus3Char7ConicAndQuartic729193;
import "conic_char7_7281113.m" : Genus3Char7ConicAndQuartic7281113;
import "conic_char7_7293101.m" : Genus3Char7ConicAndQuartic7293101;
import "conic_char7_7293102.m" : Genus3Char7ConicAndQuartic7293102;
import "conic_char7_7293113.m" : Genus3Char7ConicAndQuartic7293113;
import "conic_char7_72101113.m" : Genus3Char7ConicAndQuartic72101113;
import "conic_char7_8193113.m" : Genus3Char7ConicAndQuartic8193113;

/* import "conic_char7_93112113.m" : Genus3Char7ConicAndQuartic93112113; */
/* import "conic_char7_93113121.m" : Genus3Char7ConicAndQuartic93113121; */
/* import "conic_char7_93113123.m" : Genus3Char7ConicAndQuartic93113123; */



/************************************************/
/* Conique and Quartique method for the C2x2 case */
/************************************************/

function Genus3Char7ConicAndQuarticForC4(JI : models := true)

    FF := Universe(JI);

    /* Considering conics in turn */
    R, C, Q := Genus3Char7ConicAndQuartic5671(JI : models := models);
    if R eq 0 then R, C, Q := Genus3Char7ConicAndQuartic5693(JI : models := models); end if;
    if R eq 0 then R, C, Q := Genus3Char7ConicAndQuartic582113(JI : models := models); end if;

    /* No non-degenrate conic found, return immediatly (should not happen) */
    if R eq 0 then
	vprintf G3Twists, 1 : "ARGH, none non-degenerate conic found in a C4 case (this should not happen) \n";
	return false;
    end if;

    /* Computing conic and quartic */
    if models then

	PC := Parent(C);  x1 := PC.1; x2 := PC.2; x3 := PC.3;
	/* If no sparse conic or quartic found,
           return immediatly (this should not happen) */
	Cc, Cm := CoefficientsAndMonomials(C);
	if (Seqset(Cm) meet {x1^2, x2^2, x3^2, x1*x3}) ne Seqset(Cm) then
	    vprintf G3Twists, 1 : "ARGH, none sparse conic found in a C4 case (this should not happen)\n";
	    return false;
	end if;

	Qc, Qm := CoefficientsAndMonomials(Q);
	if (Seqset(Qm) meet {x2*x1^3, x2*x3^3, x2^3*x1, x2*x1^2*x3, x2^3*x3, x2*x1*x3^2}) ne Seqset(Qm) then
	    vprintf G3Twists, 1 : "ARGH, none sparse quartic found in a C4 case (this should not happen)\n";
	    return false;
	end if;

	if Index(Cm, x1^2) eq 0 then c11 := FF!0; else	c11 := Cc[Index(Cm, x1^2)]; end if;
	if Index(Cm, x2^2) eq 0 then c22 := FF!0; else c22 := Cc[Index(Cm, x2^2)];  end if;
	if Index(Cm, x3^2) eq 0 then c33 := FF!0; else c33 := Cc[Index(Cm, x3^2)];  end if;
	if Index(Cm, x1*x3) eq 0 then c13 := FF!0; else c13 := Cc[Index(Cm, x1*x3)]; end if;
	/* "c11 := ", c11, ";"; "c13 := ", c13, ";"; "c22 := ", c22, ";"; "c33 := ", c33, ";"; */

	if c11 eq 0 then
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
	    vprintf G3Twists, 1 : "ARGH, none rational model found in a C4 case (this should not happen)\n";
	end if;

	FFx := PolynomialRing(FF); x := FFx.1;

	fr :=  &+[(FF!F[1+i, 2])*x^(i) : i in [0..Degree(f)] | #F[1+i] ne 0];

	return fr;
    end if;

    return true;

end function;


/*****************************************************/
/* Conique and Quartique method for the generic case */
/*****************************************************/

function CheapIntegerSquareFreePart(i)
    Q:= Factorization(i: ECMLimit:= 10, MPQSLimit:= 0);
    _, af:= Squarefree(Q);
    a:= FactorizationToInteger(af);
    return i div a^2, a;
end function;

function CheapRationalSquareFreePart(r)
    an, bn:= CheapIntegerSquareFreePart(Numerator(r));
    ad, bd:= CheapIntegerSquareFreePart(Denominator(r));
    return an*ad, bn/(ad*bd);
end function;


/* Find an affine point (x,y,1) on the projective conic L. */
function FindPointOnConic(L)
    K:= BaseRing(Parent(L));
    UP:= PolynomialRing(K : Global:= false); u:= UP.1;
    if Type(K) eq FldFin then
	repeat
	    x1:= Random(K); x3:= K!1;
	    LL:= Evaluate(L, [UP | x1,u,x3]);
	    t, x2:= HasRoot(LL);
	until t;
	return x1,x2;
    elif Type(K) eq FldRat then
	P:= ProjectiveSpace(K, 2);
	x:= P.1; y:= P.2; z:= P.3;
	C:= Conic(P, L);
	if not HasRationalPoint(C) then
	    LC,m:= LegendreModel(C); C, LC;
	    LL:= DefiningPolynomial(LC);
	    i1:= K!Coefficient(LL,x,2);
	    i2:= K!Coefficient(LL,y,2);
	    i3:= K!Coefficient(LL,z,2);
	    b1, a1:= CheapRationalSquareFreePart(-i3/i1);
	    b2, a2:= CheapRationalSquareFreePart(-i3/i2);
	    if Abs(b1) lt Abs(b2) then
		S:= QuadraticField(b1); b:= S.1;
		Lsol:= [a1*b, 0, 1];
	    else
		S:= QuadraticField(b2); b:= S.1;
		Lsol:= [0, a2*b, 1];
	    end if;Lsol;
	    sol:= [Evaluate(p,Lsol) : p in DefiningPolynomials(Inverse(m))];
	    return sol[1]/sol[3],sol[2]/sol[3];
	else
	    found:= false;
	    repeat
		S:= Reduction(Random(C));
		if S[3] ne 0 then
		    found:= true;
		else
		    pol:= Evaluate(L, [UP | S[1],S[2],u]); // pol = c*u*(u-t)
		    if Coefficient(pol, 2) ne 0 then
			s3:= -Coefficient(pol, 1)/Coefficient(pol, 2);
			found:= true;
		    end if;
		end if;
	    until found;
	    assert Evaluate(L, Eltseq(S)) eq 0;
	    if S[3] eq 0 then
		if s3 ne 0 then return S[1]/s3, S[2]/s3; end if;
		// There is only one tangent line...
		if S[1] eq 0 then
		    pol:= Evaluate(L, [UP | S[1]+u,S[2],u]); // pol = c*u*(u-t)
		else
		    pol:= Evaluate(L, [UP | S[1],S[2]+u,u]); // pol = c*u*(u-t)
		end if;
		s3:= -Coefficient(pol, 1)/Coefficient(pol, 2);
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


function Genus3Char7ConicAndQuartic(JI : models:= true)

    FF:= Universe(JI);

    /* Considering conics in turn */
    R, C, Q:= Genus3Char7ConicAndQuartic5671(JI : models:= models);
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic5672(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic5682(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic5692(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic57172(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic57281(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic57282(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic57292(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic57293(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic59293(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic67281(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic67282(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic572113(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic593121(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic717281(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic728182(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic728191(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic729193(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic7281113(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic7293101(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic7293102(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic7293113(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic72101113(JI : models:= models); end if;
    if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic8193113(JI : models:= models); end if;

    /* if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic93112113(JI : models:= models); end if; */
    /* if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic93113121(JI : models:= models); end if; */
    /* if R eq 0 then R, C, Q:= Genus3Char7ConicAndQuartic93113123(JI : models:= models); end if; */



    /* No non-degenrate conic found, return immediatly */
    if R eq 0 then return false; end if;

    /* Computing conic and quartic */
    if models then
        xi, eta:= FindPointOnConic(C);
	QF:= Parent(eta);

	if QF ne FF then
	    vprintf G3Twists, 1 : "Conic has no rational point\n";
	end if;
	P3:= PolynomialRing(QF, 3); x1:= P3.1; x2:= P3.2; x3:= P3.3;

	pol:= Evaluate(C,[xi + x2*x1, eta + x1,1]);
	a:= Coefficient(pol,x1,2);
	b:= Coefficient(pol,x1,1);

	f:= UnivariatePolynomial(Evaluate(Q,[xi*a-x2*b,a*eta-b,a]));

	return f;
    end if;

    return true;

end function;
