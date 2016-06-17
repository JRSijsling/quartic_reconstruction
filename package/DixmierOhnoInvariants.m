/***
 *  Computes the Dixmier-Ohno invariants of a ternary quartic.
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
 *  2016 R. Lercier, C. Ritzenthaler & J. Sijsling
 */

 /***
 * Exported intrinsics.
 *
 * intrinsic DixmierOhnoInvariants(f::RngMPolElt) -> SeqEnum, SeqEnum
 * intrinsic DixmierOhnoAlgebraicInvariants(FreeJI::SeqEnum : ratsolve := true) -> SeqEnum
 *
 ********************************************************************/
import "Interpolations.m" : DixmierOhnoAlgebraicRelations;

function DerivativeSequence(f,n)
    S := [ Parent(f) | ];
    for k in [0..n] do
        g := f;
        for i in [1..n] do
            if i le k then
                g := Derivative(g,1);
            else
                g := Derivative(g,2);
            end if;
        end for;
        S[k+1] := g;
    end for;
    return S;
end function;


function Transvectant(f,g,r)
    P := Parent(f);
    if f eq 0 or g eq 0 then return P!0; end if;
    Sf := DerivativeSequence(f,r);
    Sg := DerivativeSequence(g,r);
    Tfg := P!0;
    for k in [0..r] do
         Tfg +:= (-1)^k*Binomial(r,k)*Sf[k+1]*Sg[r-k+1];
    end for;
    n := TotalDegree(f);
    m := TotalDegree(g);
    cfg := Factorial(n-r)*Factorial(m-r)/(Factorial(n)*Factorial(m));
    return cfg*Tfg;
end function;


function PowerDerivative(F,exp)
    DF := F;
    for i in [1..#exp] do
	if exp[i] ne 0 then
	    DF := Derivative(DF,exp[i],i); // k = exp[i]-th derivative wrt i
	end if;
    end for;
    return DF;
end function;


function DifferentialOperation(F,G)
    mons := Monomials(F);
    cffs := Coefficients(F);
    DG := Parent(G)!0;
    for i in [1..#cffs] do
	DG +:= cffs[i]*PowerDerivative(G,Exponents(mons[i]));
    end for;
    return DG;
end function;


function JOperation11(F,G)
    X,Y,Z := Explode([ P.i : i in [1..3] ]) where P := Parent(F);
    ww := [  1,  1/2,  1,  1/2, 1/2,  1  ];
    XX := [ X^2, X*Y, Y^2, Y*Z, X*Z, Z^2 ];
    FF := [ MonomialCoefficient(F,M) : M in XX ];
    GG := [ MonomialCoefficient(G,M) : M in XX ];
    return &+[ ww[i]*FF[i]*GG[i] : i in [1..6] ];
end function;


function JOperation22(F,G)
    P := Parent(F);
    K := BaseRing(P);
    X,Y,Z := Explode([ P.i : i in [1..3] ]);
    A := MatrixAlgebra(K,3)!0;
    B := MatrixAlgebra(K,3)!0;
    for i in [1..3] do
	A[i,i] := MonomialCoefficient(F,P.i^2);
	B[i,i] := MonomialCoefficient(G,P.i^2);
	for j in [i+1..3] do
	    A[i,j] := MonomialCoefficient(F,P.i*P.j)/2;
	    A[j,i] := A[i,j];
	    B[i,j] := MonomialCoefficient(G,P.i*P.j)/2;
	    B[j,i] := B[i,j];
	end for;
    end for;
    Astar := Eltseq(Adjoint(A));
    Bstar := Eltseq(Adjoint(B));
    return &+[ Astar[i]*Bstar[i] : i in [1..9] ];
end function;


function JOperation30(F)
    P := Parent(F);
    K := BaseRing(P);
    X,Y,Z := Explode([ P.i : i in [1..3] ]);
    A := MatrixAlgebra(K,3)!0;
    for i in [1..3] do
	A[i,i] := MonomialCoefficient(F,P.i^2);
	for j in [i+1..3] do
	    A[i,j] := MonomialCoefficient(F,P.i*P.j)/2;
	    A[j,i] := A[i,j];
	end for;
    end for;
    return K!Determinant(A);
end function;


function JOperation03(G)
    return JOperation30(G);
end function;


function CovariantHessian(Phi)
    DPhi_i := [ Derivative(Phi,i) : i in [1..3] ];
    DPhi_ij := MatrixAlgebra(Parent(Phi),3)!0;
    for i in [1..3] do
	DPhi_ij[i,i] := Derivative(DPhi_i[i],i);
	for j in [i+1..3] do
	    DPhi_ij[i,j] := Derivative(DPhi_i[i],j);
	    DPhi_ij[j,i] := DPhi_ij[i,j];
	end for;
    end for;
    return Determinant(DPhi_ij);
end function;


function ContravariantSigmaAndPsi(Phi)
    // Input: Homogeneous ternary quartic.
    // Output: Contravariants Sigma and Psi of Dixmier & Ohno
    // (Salmon 3rd ed. p. 78). These should really be in the
    // dual ring PUVW, but we return them in PXYZ.
    PXYZ := Parent(Phi);
    XYZ_orig := [ PXYZ.i : i in [1..3] ];
    K := BaseRing(PXYZ);
    PUVW<u,v,w> := PolynomialRing(K,3);
    PXYZUVW<X,Y,Z> := PolynomialRing(PUVW,3);
    L := u*X + v*Y + w*Z;
    Q := Evaluate(Phi,[X,Y,Z]);
    R := Resultant(Q,L,3);
    R := (-1)^Degree(Q,Z)*Resultant(Q,L,Z);
    // This definition of Psi follows Dixmier; there is also
    // the 'symbolic notation' of Salmon, p. 78 & p. 271 as
    // \psi = (a12)^2(a23)^2(a31)^2.
    A := MonomialCoefficient(R,X^4);
    B := (1/4)*MonomialCoefficient(R,X^3*Y);
    C := (1/6)*MonomialCoefficient(R,X^2*Y^2);
    D := (1/4)*MonomialCoefficient(R,Y^3*X);
    E := MonomialCoefficient(R,Y^4);
    Psi := Determinant(Matrix(3,[A,B,C,B,C,D,C,D,E]));
    //Psi := Evaluate(Numerator(Psi/w^(TotalDegree(Psi)-6)),XYZ_orig);
    totdeg := TotalDegree(Psi)-6;
    if totdeg ge 0 then
        Psi := Evaluate(PUVW!(Psi/w^totdeg),XYZ_orig);
    else
        Psi := Evaluate(PUVW!(Psi*w^(-totdeg)),XYZ_orig);
    end if;
    // This definition of Sigma follows Salmon's 'symbolic notation' (a12)^4.
    Pxy<x,y> := PolynomialRing(PUVW,2);
    Rxy := Evaluate(R,[x,y,0]);
    Tr:=Transvectant(Rxy,Rxy,4);
    if Tr ne 0 then
        Sigma := (1/2)*PUVW!Coefficients(Tr)[1];
    else
        Sigma := PUVW!0;
    end if;
    //Sigma := Evaluate(Numerator(Sigma/w^(TotalDegree(Sigma)-4)),XYZ_orig);
    totdeg := TotalDegree(Sigma)-4;
    if totdeg ge 0 then
        Sigma := Evaluate(PUVW!(Sigma/w^totdeg),XYZ_orig);
    else
        Sigma := Evaluate(PUVW!(Sigma*w^(-totdeg)),XYZ_orig);
    end if;
    return Sigma, Psi;
end function;


function Rho(Phi)
    _, Psi := ContravariantSigmaAndPsi(Phi);
    return    (1/144)*DifferentialOperation(Phi, Psi);
end function;

function Tau(Phi)
    return (1/12)*DifferentialOperation(Rho(Phi), Phi);
end function;

function Xi(Phi)
    Sigma, _ := ContravariantSigmaAndPsi(Phi);
    He       := (1/1728)*CovariantHessian(Phi);
    return      (1/72)*DifferentialOperation(Sigma, He);
end function;


function QuarticDiscriminant(Phi)
    P := Parent(Phi);
    K := BaseRing(P);
    X,Y,Z := Explode([ P.i : i in [1..3] ]);

    CLASSICAL := true;

    if CLASSICAL then
	C1 := (1/4)*Derivative(Phi,X);
	C2 := (1/4)*Derivative(Phi,Y);
	C3 := (1/4)*Derivative(Phi,Z);
    else
	C1 := Derivative(Phi,X);
	C2 := Derivative(Phi,Y);
	C3 := Derivative(Phi,Z);
    end if;

    C1X2 := X^2*C1;
    C2X2 := X^2*C2;
    C3X2 := X^2*C3;
    C1Y2 := Y^2*C1;
    C2Y2 := Y^2*C2;
    C3Y2 := Y^2*C3;
    C1Z2 := Z^2*C1;
    C2Z2 := Z^2*C2;
    C3Z2 := Z^2*C3;
    C1YZ := Y*Z*C1;
    C2YZ := Y*Z*C2;
    C3YZ := Y*Z*C3;
    C1ZX := Z*X*C1;
    C2ZX := Z*X*C2;
    C3ZX := Z*X*C3;
    C1XY := X*Y*C1;
    C2XY := X*Y*C2;
    C3XY := X*Y*C3;

    if CLASSICAL then
	He := (1/1728)*CovariantHessian(Phi);
    else
	He := (1/54)*CovariantHessian(Phi);
    end if;

    if CLASSICAL then
	DHe1 := (1/2)*Derivative(He,X);
	DHe2 := (1/2)*Derivative(He,Y);
	DHe3 := (1/2)*Derivative(He,Z);
    else
	DHe1 := Derivative(He,X);
	DHe2 := Derivative(He,Y);
	DHe3 := Derivative(He,Z);
    end if;

    Eqq := [
	DHe1,DHe2,DHe3,
	C1X2,C2X2,C3X2,
	C1Y2,C2Y2,C3Y2,
	C1Z2,C2Z2,C3Z2,
	C1YZ,C2YZ,C3YZ,
	C1ZX,C2ZX,C3ZX,
	C1XY,C2XY,C3XY];

    L := [
	X^5,
	X^4*Y,
	X^4*Z,
	X^3*Y^2,
	X^3*Y*Z,
	X^3*Z^2,
	X^2*Y^3,
	X^2*Y^2*Z,
	X^2*Y*Z^2,
	X^2*Z^3,
	X*Y^4,
	X*Y^3*Z,
	X*Y^2*Z^2,
	X*Y*Z^3,
	X*Z^4,
	Y^5,
	Y^4*Z,
	Y^3*Z^2,
	Y^2*Z^3,
	Y*Z^4,
	Z^5
	];
    R27 := Matrix(K,[ [MonomialCoefficient(Eqql,Ll): Ll in L]: Eqql in Eqq ]);
    return Determinant(R27);
end function;


function DixmierInvariant(Phi,i :IntegralNormalization := false)
    P := Parent(Phi);
    K := BaseRing(P);
    if i eq 27 then
	I27 := QuarticDiscriminant(Phi);
	if IntegralNormalization then
	    I27 *:= 1099511627776;
	end if;
	return I27;
    end if;
    X := P.1; Y := P.2; Z := P.3;

    a0 := MonomialCoefficient(Phi,X^4);
    b0 := (1/4)*MonomialCoefficient(Phi,X^3*Y);
    c0 := (1/6)*MonomialCoefficient(Phi,X^2*Y^2);
    d0 := (1/4)*MonomialCoefficient(Phi,Y^3*X);
    e0 := MonomialCoefficient(Phi,Y^4);
    f0 := (1/4)*MonomialCoefficient(Phi,X^3*Z);
    g0 := (1/12)*MonomialCoefficient(Phi,X^2*Y*Z);
    h0 := (1/12)*MonomialCoefficient(Phi,X*Y^2*Z);
    i0 := (1/4)*MonomialCoefficient(Phi,Y^3*Z);
    j0 := (1/6)*MonomialCoefficient(Phi,X^2*Z^2);
    k0 := (1/12)*MonomialCoefficient(Phi,X*Y*Z^2);
    l0 := (1/6)*MonomialCoefficient(Phi,Y^2*Z^2);
    m0 := (1/4)*MonomialCoefficient(Phi,X*Z^3);
    n0 := (1/4)*MonomialCoefficient(Phi,Z^3*Y);
    p0 := MonomialCoefficient(Phi,Z^4);

    if i eq 3 then
	I03 := a0*e0*p0
	    + 3*(a0*l0^2+e0*j0^2+p0*c0^2)
	    + 4*(b0*i0*m0+f0*d0*n0)
	    - 4*(a0*i0*n0+e0*f0*m0+p0*b0*d0)
	    + 6*c0*j0*l0
	    + 12*(c0*k0^2+j0*h0^2+l0*g0^2)
	    - 12*g0*h0*k0
	    - 12*(b0*k0*l0+f0*h0*l0+d0*k0*j0+i0*g0*j0+m0*h0*c0+n0*g0*c0)
	    + 12*(g0*d0*m0+h0*n0*b0+k0*f0*i0);
	if IntegralNormalization then
	    I03 *:= 144;
	end if;
	return I03;
    elif i eq 6 then
	I06 := Determinant(M) where M :=Matrix(6,6, [
	    a0,c0,j0,g0,f0,b0,
	    c0,e0,l0,i0,h0,d0,
	    j0,l0,p0,n0,m0,k0,
	    g0,i0,n0,l0,k0,h0,
	    f0,h0,m0,k0,j0,g0,
	    b0,d0,k0,h0,g0,c0]);
	if IntegralNormalization then
	    I06 *:= 2985984;
	end if;
	return I06;
    end if;

    PXYZ := Parent(Phi);
    XYZ_orig := [ PXYZ.i : i in [1..3] ];
    K := BaseRing(PXYZ);
    PUVW<u,v,w> := PolynomialRing(K,3);
    PXYZUVW<X,Y,Z> := PolynomialRing(PUVW,3);
    Q := Evaluate(Phi,[X,Y,Z]);
    L := u*X+v*Y+w*Z;

    R := Resultant(Q,L,Z);
    R := (-1)^Degree(Q,Z)*Resultant(Q,L,Z);

    A0 := MonomialCoefficient(R,X^4);
    B0 := (1/4)*MonomialCoefficient(R,X^3*Y);
    C0 := (1/6)*MonomialCoefficient(R,X^2*Y^2);
    D0 := (1/4)*MonomialCoefficient(R,Y^3*X);
    E0 := MonomialCoefficient(R,Y^4);

    Psi := Determinant(Matrix(3,[A0,B0,C0,B0,C0,D0,C0,D0,E0]));
    Psi := Evaluate(PUVW!Numerator(Psi/w^(TotalDegree(Psi)-6)),XYZ_orig);

    Rho := (1/144)*DifferentialOperation(Phi,Psi);
    Tau := (1/12)*DifferentialOperation(Rho,Phi);

    Xo, Yo, Zo := Explode(XYZ_orig);
    A1 := MonomialCoefficient(Tau,Xo^2);
    B1 := (1/2)*MonomialCoefficient(Tau,Xo*Yo);
    C1 := MonomialCoefficient(Tau,Yo^2);
    D1 := (1/2)*MonomialCoefficient(Tau,Xo*Zo);
    E1 := (1/2)*MonomialCoefficient(Tau,Yo*Zo);
    F1 := MonomialCoefficient(Tau,Zo^2);

    A2 := MonomialCoefficient(Rho,Xo^2);
    B2 := (1/2)*MonomialCoefficient(Rho,Xo*Yo);
    C2 := MonomialCoefficient(Rho,Yo^2);
    D2 := (1/2)*MonomialCoefficient(Rho,Xo*Zo);
    E2 := (1/2)*MonomialCoefficient(Rho,Yo*Zo);
    F2 := MonomialCoefficient(Rho,Zo^2);

    if i eq 9 then
	I09 := A1*A2+2*B1*B2+C1*C2+2*D1*D2+2*E1*E2+F1*F2;
	if IntegralNormalization then
	    I09 *:= 26873856;
	end if;
	return K!I09;
    elif i eq 12 then
	I12 := Determinant(Matrix(3,3,[A2,B2,D2,B2,C2,E2,D2,E2,F2]));
	if IntegralNormalization then
	    I12 *:= 34828517376;
	end if;
	return K!I12;
    elif i eq 15 then
	I15 := Determinant(Matrix(3,3,[A1,B1,D1,B1,C1,E1,D1,E1,F1]));
	if IntegralNormalization then
	    I15 *:= 120367356051456;
	end if;
//	return K!MonomialCoefficient(I15,PUVW!1);
	return K!I15;
    elif i eq 18 then
	I18 := (E1^2-C1*F1)*(E2^2-C2*F2)+2*(B1*F1-D1*E1)*(B2*F2-D2*E2)
	    + (D1^2-A1*F1)*(D2^2-A2*F2) + 2*(C1*D1-B1*E1)*(C2*D2-B2*E2)
	    + 2*(A1*E1-B1*D1)*(A2*E2-B2*D2)+(B1^2-A1*C1)*(B2^2-A2*C2);
	if IntegralNormalization then
	    I18 *:= 17332899271409664;
	end if;
//	return K!MonomialCoefficient(I18,PUVW!1);
	return K!I18;
    end if;
end function;

intrinsic DixmierOhnoInvariants(f::RngMPolElt : normalize := false) -> SeqEnum, SeqEnum
    {
    Compute the 13 Dixmier-Ohno invariants 'I3', 'I6', 'I9', 'J9', 'I12',
    'J12', 'I15', 'J15', 'I18', 'J18', 'I21', 'J21' and 'I27' of a quartic
    given as a binary (or a ternary homogeneous) polynomial of degree 4.

    The characteristic of the coefficient ring must be 0 or greater than 7.

    Weights of these invariants are returned too.
    }

    P := Parent(f);

    require
	Rank(P) in {2, 3} and
	((Rank(P) eq 3 and {Degree(e) : e in Monomials(f)} eq {4}) or
	(Rank(P) eq 2 and Degree(f) le 4))
	:
	"Input must be a ternary homogeneous polynomial of degree  4 or a binary polynomial of degree <= 4";

    require
	(Characteristic(P) eq 0) or (Characteristic(P) gt 7)
	:
	"Characteristic must be 0 or > 7";

    Phi := f;
    if Rank(P) eq 2 then
	Phi := Basis(Homogenization(ideal<Parent(f)|f>))[1];
	P := Parent(Phi);
    end if;

    Sigma, Psi := ContravariantSigmaAndPsi(Phi);
    Rho := (1/144)*DifferentialOperation(Phi,Psi);
    He := (1/1728)*CovariantHessian(Phi); // deg = 3, ord = 6
    Tau := (1/12)*DifferentialOperation(Rho,Phi);
    Xi := (1/72)*DifferentialOperation(Sigma,He);
    Eta := (1/12)*DifferentialOperation(Xi,Sigma);
    //    Chi := (1/8)*DifferentialOperation(Tau,DifferentialOperation(Tau,Psi));
    Nu := (1/8)*DifferentialOperation(Eta,DifferentialOperation(Rho,He));
    I03 := DixmierInvariant(Phi,3 : IntegralNormalization := false);
    I06 := DixmierInvariant(Phi,6 : IntegralNormalization := false);
    //   J06 := DifferentialOperation(Psi,He);
    I09 := JOperation11(Tau,Rho);
    J09 := JOperation11(Xi,Rho); // Ohno
    I12 := JOperation03(Rho);
    J12 := JOperation11(Tau,Eta); // Ohno
    I15 := JOperation30(Tau);
    J15 := JOperation30(Xi); // Ohno
    I18 := JOperation22(Tau,Rho);
    J18 := JOperation22(Xi,Rho); // Ohno
    I21 := JOperation03(Eta); // Ohno
    J21 := JOperation11(Nu,Eta); // Ohno
    I27 := QuarticDiscriminant(Phi);
    //   J27 := JOperation11(Nu,Chi); // Ohno (not given name) not returned

    ww := [3*w : w in [1,2,3,3,4,4,5,5,6,6,7,7,9]];
    DD := [I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27];

    if normalize eq false then return DD, ww; end if;
    return WPSNormalize(ww, DD), ww;

end intrinsic;

/* From g3twists/sl2invtools */
function PowerRepresentativesInFiniteFields(FF, pow)
    R := [FF!1]; NB := #AllRoots(FF!1, pow);
    for w in FF do
	if #R eq NB then break; end if;
	if &and[ not IsPower(w / r, pow) : r in R] then
	    Append(~R, w);
	end if;
    end for;
    return R;
end function;

function InvariantsAppend(LST, JI)
    old := false;
    for oldjis in LST do
	if WPSEqual([ 3, 6, 9, 9, 12, 12, 15, 15, 18, 18, 21, 21, 27 ], oldjis, JI) then
	    old := true; break;
	end if;
    end for;
    if not old then return Append(LST, JI); end if;
    return LST;
end function;

intrinsic DixmierOhnoAlgebraicInvariants(FreeJI::SeqEnum : ratsolve := true) -> SeqEnum
    {
    This function returns the algebraic relations between the seven primary
    invariants given in input and the other Dixmier-Ohno invariants.

    In Characteristic 0 or > 7, the primary invariants are 'I3', 'I6', 'I9',
    'I12', 'I15', 'I18' and 'I27.

    By default (ratsolve := true), this function computes solutions to
    the system of relations and returns them as a list of invariants. Otherwise
    (ratsolve := false), the system is returned as is.
    }

    FF := Universe(FreeJI); p := Characteristic(FF);

    require
	(Characteristic(FF) eq 0) or (Characteristic(FF) gt 7)
	:
	"Characteristic must be 0 or > 7";

    require #FreeJI eq 7
	:
	"Argument must be a sequence of seven free Dixmier Ohno invariants I3, I6, I9, I12, I15, I18 and I27.";

    if Universe(FreeJI) cmpeq Integers() then
	ChangeUniverse(~FreeJI, Rationals());
    end if;

    FWeights := [3, 6, 9, 12, 15, 18, 27];

    if ratsolve eq false or not IsFinite(FF) then
	g := 1; LG := [ FF!1 ];
    else
	Support := [i : i in [1..#FreeJI] | FreeJI[i] ne 0];
	if #Support eq 0 then
	    g := 1;
	    LG := [ FF!1 ];
	else
	    g := Gcd([FWeights[i] : i in Support]);
	    LG := PowerRepresentativesInFiniteFields(FF, g);
	end if;
    end if;

    P6 := PolynomialRing(FF, 6); J09 := P6.1; J12 := P6.2; J15 := P6.3; J18 := P6.4; I21 := P6.5; J21 := P6.6;

    JIs := [];
    for L in LG do

	I03, I06, I09, I12, I15, I18, I27 := Explode([L^(FWeights[i] div g) * FreeJI[i] : i in [1 .. #FreeJI]]);

	RELs := DixmierOhnoAlgebraicRelations([I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27]);

	if ratsolve eq false then return RELs; end if;

	V := Variety(ideal<P6 | RELs>);
	for v in V do
	    j09, j12, j15, j18, i21, j21 := Explode([_v : _v in v]);
	    NJI := WPSNormalize(
		[ 3, 6, 9, 9, 12, 12, 15, 15, 18, 18, 21, 21, 27 ],
		[ I03, I06, I09, j09, I12, j12, I15, j15, I18, j18, i21, j21, I27 ]
		);
	    JIs := InvariantsAppend(JIs, NJI);
	end for;
    end for;

    return JIs;

end intrinsic;
