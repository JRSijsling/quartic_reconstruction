/***
 *  Compute a quartic with given Dixmier-Ohno invariants, when I_12 does not
 *  equal 0.
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
 *  Copyright 2016 R. Lercier, C. Ritzenthaler & J.R. Sijsling
 */

/* This code may fail in two places :

  _ in HyperellipticPolynomialFromJointShiodaInvariants, when the
    reconstructed octic has a (geom.) automorphism group equal to C14
    (to be checked, but it probably means that the quartic is singular)

  _ in DixmierOhnoToBinaryQuartic, when both the joint invariant constraints
    and the normalized contravariant constraints are not enough to get a fixed
    number of solutions. (but I never encoutered such a problem).

*/

import "DixmierOhnoInvariants.m":
    Rho, DixmierInvariant;
import "TernaryForms.m":
    TernaryToBinary, BinaryToTernary, Homogenization;
import "JointCovariants.dat":
    S8S4Cov;
import "JointCovariants.m":
    IthJointInvariant, JointCovariant,
    FirstJointInvariants, JointShiodaInvariants;
import "Interpolations.m":
    JointInvariantFromDixmierOhno;
import "Descent.m":
    Descent;
import "AutStrataChar0Equations.m":
    IsInStratumC9, IsInStratumG48, IsInStratumG96, IsInStratumG168,
    IsInStratumC6, IsInStratumG16, IsInStratumS4, IsInStratumC3,
    IsInStratumD8, IsInStratumS3, IsInStratumD4;
import "AutStrataChar0Reconstruction.m":
    TernaryQuartic_S3_I12eq0, TernaryQuartic_C3,
    TernaryQuartic_D8_I12eq0, TernaryQuartic_D4_I12eq0;

declare verbose Reconstruction, 2;


forward XGCDUnique;
forward HyperellipticPolynomialFromJointShiodaInvariants;
forward DixmierOhnoToJointShioda;
forward DixmierOhnoToBinaryQuartic;

intrinsic TernaryQuarticFromDixmierOhnoInvariantsI12ne0(DO::SeqEnum : exact := false, minimize := true, descent := true, search_point := true) -> RngMPolElt, SeqEnum
    {Reconstructs a ternary quartic from a given tuple of Dixmier-Ohno
    invariants DO, and also returns the binary forms associated to it by the
    usual equivariant morphism. The invariant I12 is supposed to be not equal
    to zero.

    If the flag exact is set to true, then a ternary forms is returned whose
    Dixmier-Ohno invariants exactly equal DOInv (instead of merely being
    equal in the corresponding weighted projective space).
    
    If the flag descent is set to true, then the curve is descended to its base
    field.
    
    If the flag minimize is set to true, then over the rationals an effort is
    made to return as small a model as possible.
    
    If the flag search_point is set to true, then the algorithm tries to find a
    rational point of the Mestre conic of the associated binary form.}

    vprint Reconstruction : "Start of quartic reconstruction.";
    F := Parent(DO[1]);
    ratbase := (Characteristic(F) eq 0) and (F eq Rationals());
    bp0 := [];
    if ratbase then
        vprint Reconstruction : "Factorizing numerator and denominator of I12...";
        I12 := DO[5];
        Fac_num := Factorization(Numerator(I12));
        Fac_den := Factorization(Denominator(I12));
        bp0_new := Sort([ fac[1] : fac in Fac_num ] cat [ fac[1] : fac in Fac_den ]);
        bp0 := Sort(bp0 cat [ p : p in bp0_new | not p in bp0 ]);
        vprint Reconstruction : bp0;
    end if;

    vprint Reconstruction : "Determining joint Shioda invariants from Dixmier-Ohno invariants...";
    JointShioda := DixmierOhnoToJointShioda(DO);

    vprint Reconstruction, 2 : "Joint Shioda invariants:", JointShioda;
    if ratbase then
        WJS := [2..10];
        JointShioda, lambda1 := WPSMinimize(WJS, JointShioda);
        vprint Reconstruction, 2 : "Joint Shioda invariants after minimization:", JointShioda;
    else
        lambda1 := Parent(DO[1]) ! 1;
    end if;

    vprint Reconstruction : "Reconstructing binary octic b_8...";
    b8, lambda2 := HyperellipticPolynomialFromJointShiodaInvariants(JointShioda : search_point := search_point);
    b8 *:= (1/lambda1) * lambda2;
    /* Alternative version: */
    //b8 *:= lambda2;

    if b8 eq 0 then
	error "[DixmierOhnoToQuartic] b_8 has a root of order >= 4, not yet implemented";
    end if;

    vprint Reconstruction : "Reconstructed binary octic b_8:", Homogenization(b8 : degree := 8);

    vprint Reconstruction : "Reconstructing binary quartic b_4...";
    b4 := DixmierOhnoToBinaryQuartic(DO, b8);
    /* Alternative version: */
    //b4 := DixmierOhnoToBinaryQuartic(DO, b8 : lambda := lambda1);
    vprint Reconstruction : "Reconstructed binary quartic b_4:", Homogenization(b4 : degree := 4);

    S := PolynomialRing(CoefficientRing(b4), 2);
    b8h := S ! Homogenization(b8 : degree := 8);
    b4h := S ! Homogenization(b4 : degree := 4);
    b0h := S ! DO[3];
    /* Alternative version: */
    //b0h := S ! (lambda1^(-8) * DO[3]);
    vprint Reconstruction : "Reconstructed constant b_0:", b0h;

    vprint Reconstruction : "Final inversion...";
    if not descent or &and( &cat[ [ coeff in F : coeff in Coefficients(b) ] : b in [ b8h, b4h, b0h ] ] ) then
        R<x1, x2, x3> := PolynomialRing(F, 3);
        f := R ! BinaryToTernary([b8h, b4h, b0h]);
    else
        f := BinaryToTernary([b8h, b4h, b0h]);
        vprint Reconstruction : "Descending...";
	R<x1, x2, x3> := PolynomialRing(F, 3);
        f, bp0_new := Descent(f, b8 : RandomCoboundary := true, SmallCoboundary := minimize);
        f := R ! f;
        bp0 := Sort(bp0 cat [ p : p in bp0_new | not p in bp0 ]);
    end if;

    /* Simplify over the rationals by removing content and apply MinimizeReduce : */
    if ratbase then
        gcd_den := GCD([ Denominator(coeff) : coeff in Coefficients(f) ]);
        gcd_num := GCD([ Numerator(coeff) : coeff in Coefficients(f) ]);
        f *:= (gcd_den/gcd_num);
        lcm_num := LCM([ Denominator(coeff) : coeff in Coefficients(f) ]);
        f *:= lcm_num;
        vprint Reconstruction : "A first model over the rationals is given by";
        vprint Reconstruction : f;
        if minimize then
            vprint Reconstruction : "Reducing coefficients...";
            f := MinimizeReducePlaneQuartic(f : BadPrimesList := bp0, ImproveFurther := true);
        end if;
        R<x1, x2, x3> := PolynomialRing(F, 3);
        f := R ! f;
    end if;

    if not exact then
        return f, TernaryToBinary(f);
    else
        /* Scale via the 3-4 trick: */
        W := [ 3, 6, 9, 9, 12, 12, 15, 15, 18, 18, 21, 21, 27 ];
        indices := [ i : i in [1..#DO] | DO[i] ne 0 ];
        gcd, L := XGCDUnique([ W[i] : i in indices ]);
        I := DixmierOhnoInvariants(f);
        lambda3 := &*[ (DO[i] / I[i])^(L[i]) : i in indices ];
        f := (1/lambda3) * Evaluate(f, [ lambda3*x1, x2, x3 ]);
        return f, TernaryToBinary(f);
    end if;
end intrinsic;


function XGCDUnique(L)
    /* Extended GCD algorithm that is more compatible with list extension.
     * The final result is the GCD of the elmements in the list along with a
     * way to obtain it from the elements. */

    if #L eq 0 then
        /* JRS: Changed this to 1 because it makes sense to me  :-/  */
	return 1, [];
    end if;

    if #L eq 1 then
	return L[1], [Universe(L)!1];
    end if;

    g := GCD(L); C := [Universe(L)!0 : c in L];

    gc, C[1], C[2] := XGCD(L[1], L[2]); idx := 2;
    while gc ne g do
	idx +:= 1;
	gc, x, C[idx] := XGCD(gc, L[idx]);
	for i := 1 to idx-1 do
	    C[i] *:= x;
	end for;
    end while;

    return g, C;

end function;


function HyperellipticPolynomialFromJointShiodaInvariants(JS : search_point := true)

    vprint Reconstruction : "Converting joint invariants to Shioda invariants...";
    S2, S3, S4, S5, S6, S7, S8, S9, S10 := Explode(ShiodaInvariantsFromJointShiodaInvariants(JS));
    vprint Reconstruction, 2 : "Shioda invariants:", [S2, S3, S4, S5, S6, S7, S8, S9, S10];

    /* b8 has a root of order 4, not yet implemented */
    if  S10 - 125/941192*S2^5 eq 0 and
	S9 - 625/111132*S3*S2^3 eq 0 and
	S8 - 75/67228*S2^4 eq 0 and
	S7 - 125/2646*S3*S2^2 eq 0 and
	S6 - 125/12348*S2^3 eq 0 and
	S5 - 25/63*S3*S2 eq 0 and
	S4 - 25/294*S2^2 eq 0 and
	S3^2 - 81/3430*S2^3 eq 0
	then
	return 0, 0;
    end if;

    vprint Reconstruction : "Determining non-twisted binary octic from Shioda invariants...";
    b8 := HyperellipticPolynomialFromShiodaInvariants([S2, S3, S4, S5, S6, S7, S8, S9, S10] : RationalModel := search_point);
    K := BaseRing(Parent(b8));
    r := K.1;
    vprint Reconstruction, 2 : "Reconstructed non-twisted binary octic:", Homogenization(b8 : degree := 8);

    /* Extracting gcd of indices with non-zero invariant */
    Idx := [i : i in [1..9] | IsUnit(JS[i]) ];
    g, C := XGCDUnique([[2, 3, 4, 5, 6, 7, 8, 9, 10][i] : i in Idx]);

    /* Recalculate joint invariants to get exact values;
     * note that bs does not in general get all indices defined, only those in
     * Idx */
    bs := []; for i := 1 to #Idx do
	if C[i] ne 0 then
	    bs[Idx[i]] := Parent(JS[1])!IthJointInvariant(S8S4Cov, [0*b8, b8], Idx[i]);
	end if;
    end for;
    vprint Reconstruction, 2 :
	"Joint Shioda Invariants of b8 in used:",
	[ [* i, bs[Idx[i]] *] : i in [1..#Idx] | C[i] ne 0 ];

    vprint Reconstruction : "Recovering the twisting scalar...";
    /* Recovering the twisting scalar */
    lbdinvpowg := 1; for j := 1 to #Idx do
	if C[j] ne 0 then
	    lbdinvpowg *:= (bs[Idx[j]] / JS[Idx[j]]) ^ C[j];
	end if;
    end for;

    /* Case of coprime joint invariant weights is easier: */
    if g eq 1 then
        vprint Reconstruction, 2 : "Twisting scalar:", lbdinvpowg;
	return b8, 1/lbdinvpowg;
    end if;

    /* The case left is where we have to take an extension;
     * here we can have g = 2, or g = 7
     * (otherwise, the discriminant of b8 is 0) */
    ret, lbdinv := IsPower(lbdinvpowg, g);
    if ret then	return b8, 1/lbdinv; end if;

    FF := Universe(JS); x := PolynomialRing(FF).1;
    Ft := Sort(Factorization(x^g - lbdinvpowg), func<x, y| Degree(x[1]) - Degree(y[1])>);
    Pl := Ft[1, 1]; Pl /:= Coefficient(Pl, Degree(Pl));

    if IsFinite(FF) or Type(FF) eq FldRat or IsNumberField(FF) then
	Kl := ext<FF | Pl>;
    else
	Kl := quo<Parent(x) | Pl>;
    end if;

    vprint Reconstruction : "An extension of the base field of the binary octic was required to obtain the twisting scalar.";
    vprint Reconstruction, 2 : "Twisting scalar:", 1/Kl.1;
    return (PolynomialRing(Kl)!b8), 1/Kl.1;

end function;


function DixmierOhnoToJointShioda(DO)

    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27 := Explode(DO);
    FirstJointShiodaNames := [ "s2", "s3", "s4", "s5", "s6", "s7", "s8" ];
    FirstJointShiodaInvs := [ JointInvariantFromDixmierOhno(s, DO) : s in FirstJointShiodaNames ];
    s2, s3, s4, s5, s6, s7, s8 := Explode(FirstJointShiodaInvs);

    /* Use Shioda's relations if possible: */

    A1 := (-15057862236041625*s2^3+10586619521478000*s2*s4-421058730967875*s3^2+11909946961662750*s6);
    B1 := (837691470000000*s3*s2^2+1979046097875000*s5*s2-552876370200000*s4*s3-5473476064980000*s7);
    C1 := (219542180457600*s6^2*s4-9907544553984000*s8*s4^2+45796108050000*s6*s5^2+23559905055456*s7^2*s2-245385723844800*s6^2*s2^2-4209541245000*s5^2*s3^2-1671727559040*s7*s3^3-21351486340800000*s8*s2^4+464802770361600*s4^2*s2^4-315614488780800*s4^3*s2^2-138561496053750*s5^2*s2^3-234163583174400*s4*s2^6+25708012753500*s6*s5*s3*s2-57134281327200*s7*s4*s3*s2-24590821563000*s5*s4*s3*s2^2+167189814348480000*s8^2+71891479756800*s4^4+6677771840000*s2^8+43553980377600*s4*s3^2*s2^3+90467790557760*s7*s3*s2^3-396864710827200*s6*s4*s2^3+37689876840000*s6*s3^2*s2^2+291156631920000*s6*s2^5-32696947360000*s3^2*s2^5-249967134648000*s7*s5*s4-268670500560000*s8*s5*s3-24875318714400*s6*s4*s3^2+11142142704000*s5*s4^2*s3+8190612117072000*s8*s6*s2+131088330450000*s5^2*s4*s2+135102880281600*s6*s4^2*s2-14502836779200*s4^2*s3^2*s2+604446948000*s5*s3^3*s2+214566800817600*s7*s5*s2^2+29103412127328000*s8*s4*s2^2+10269604338000*s5*s3*s2^4-122139884013840*s7*s6*s3);

    A2 := (-24060498912450000*s3*s2^2-56842928680663125*s5*s2+15879929282217000*s4*s3+157211299893948300*s7);
    B2 := (898723277100000*s2^4-30289726853100000*s2^2*s4-1231406460900000*s2*s3^2-3731915498850000*s2*s6+11874276587250000*s3*s5+20851337390400000*s4^2-2463064229241000000*s8);
    C2 := (-8911001915200*s2^7*s3-72193200187680*s2^5*s7-376100323200*s2*s3^5+57691563909000*s2^6*s5-20410965758400*s2^4*s3^3-874289335500000*s2*s5^3-1253795669280000*s3^3*s8-334438346880000*s4^3*s5-2496701227603968*s3*s7^2+2418034505040000*s5^2*s7-725410351512000*s5*s6^2-169595235532800*s2^2*s3*s4*s6+140629859370000*s2*s3^2*s4*s5-3926427458184000*s2*s3*s4*s8+199647769582800*s2*s3*s5*s7-1068559239132000*s2*s4*s5*s6+5641504848000*s3^4*s5-7960607424000*s3^3*s4^2+305786600196000*s2^5*s3*s4-43788923732400*s2^4*s3*s6-1958797173069000*s2^4*s4*s5-275361106923000*s2^3*s3^2*s5-390714419541600*s2^3*s3*s4^2+26691152796000*s2^2*s3^3*s4+8874655740720000*s2^3*s3*s8+2433131944008480*s2^3*s4*s7+1897589602408500*s2^3*s5*s6+719844560154720*s2^2*s3^2*s7+219906126247500*s2^2*s3*s5^2+1824328109736000*s2^2*s4^2*s5-18740094080400*s2*s3^3*s6+126644057971200*s2*s3*s4^3-152468909838630000*s2^2*s5*s8-3016996090693200*s2^2*s6*s7+470184037507800*s2*s3*s6^2-1674959147896320*s2*s4^2*s7-409812070187520*s3^2*s4*s7-22830207939000*s3^2*s5*s6+150054742252800*s3*s4^2*s6+53792253900000*s3*s4*s5^2+229063314690302400*s2*s7*s8+12419613734220000*s3*s6*s8+39505529725200000*s4*s5*s8+1783358019717120*s4*s6*s7);

    den := (A1*B2-A2*B1);
    if den ne 0 then
        s9 := -(A1*C2-A2*C1) / den;
        s10 := (B1*C2-B2*C1) / den;
    else
        s9 := JointInvariantFromDixmierOhno("s9", DO);
        s10 := JointInvariantFromDixmierOhno("s10", DO);
    end if;

    return FirstJointShiodaInvs cat [ s9, s10 ];

end function;


function DixmierOhnoToBinaryQuartic(DO, b8 : lambda := 1);
    /* Coefficient ring plus deformation: */
    Pa<a0, a1, a2, a3, a4> := PolynomialRing(CoefficientRing(b8), 5);
    Pt := PolynomialRing(Pa); t := Pt.1;

    /* JRS: I trust you (so I have not changed anything) but I am a bit afraid
     * of using these rings because coercion occurs later */
    A0, A1, A2, A3, A4 := Explode([Pa.i : i in [1..5]]);
    B4 := Pt ! [A0, A1, A2, A3, A4];
    B8 := Pt ! Coefficients(b8);

    /* We know proceed to use the invariants that give linear relations */
    vprint Reconstruction : "Trying with linear relations only...";

    LinearJointInvsNames := [ "j3", "j4c", "j5e", "j5f", "j6h", "j6i" ];
    LinearJointInvsIndices := [ 74, 79, 85, 86, 95, 96 ];
    LinearJointInvsWeights := [ 3, 4, 5, 5, 6, 6 ];

    LEQ := []; _Precomputations := [];
    for i:=1 to #LinearJointInvsNames do
        inv := lambda^(-8*LinearJointInvsWeights[i]) * JointInvariantFromDixmierOhno(LinearJointInvsNames[i], DO);
        COV, _Precomputations := JointCovariant(S8S4Cov, [B4, B8], LinearJointInvsIndices[i] : Precomputations :=_Precomputations);
        Append(~LEQ, Pa!(COV[1]) - inv);
    end for;

    vprint Reconstruction, 2 : "Linear constraints :", LEQ;
    II := ideal<Pa | LEQ>;

    /* Generic case */
    if Dimension(II) lt 0 then
	error "[DixmierOhnoToQuartic] Error: there is no B4 compatible with B8 and DO";
    end if;
    if Dimension(II) eq 0 then
	V := Variety(II);
	if #V eq 1 then
	    a0, a1, a2, a3, a4 := Explode(Random(V));
            vprint Reconstruction : "Linear relations suffice.";
	    b4 := Parent(b8)![a0, a1, a2, a3, a4];
            return b4;
	end if;
    end if;

    /* TODO: Check for correctness of what follows. */
    /* Strange situation, we try to add degree 2 constraints */
    vprint Reconstruction : "Adding more, non-linear, constraints...";

    QuadJointInvsNames := [ "j3a", "j4a", "j4b", "j5c", "j5d", "j6e", "j6f", "j6g" ];
    QuadJointInvsIndices := [ 75, 77, 78, 83, 84, 92, 93, 94 ];

    for i:=1 to #QuadJointInvsNames do
        inv := JointInvariantFromDixmierOhno(QuadJointInvsNames[i], DO);
        COV,_Precomputations := JointCovariant(S8S4Cov, [B4, B8], QuadJointInvsIndices[i] : Precomputations :=_Precomputations);
        Append(~LEQ,Pa!(COV[1])-inv);
    end for;

    /* In case we fail, we try to add more (but non-linear) constraints, which
     * impose that the covariant of the end result is normalized */
    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27 := Explode(DO);
    S := PolynomialRing(CoefficientRing(B4), 2); x := S.1; y := S.2;
    B8h := S ! Homogenization(B8 : degree := 8);
    B4h := S ! Homogenization(B4 : degree := 4);
    B0h := S ! I09;

    G := BinaryToTernary([B8h, B4h, B0h]);
    Q := Rho(G);
    X, Y, Z := Explode(GeneratorsSequence(Parent(Q)));
    LEQ cat:= [
	MonomialCoefficient(Q, X^2),
	MonomialCoefficient(Q, Y^2) + MonomialCoefficient(Q, X*Z),
	MonomialCoefficient(Q, Z^2),
	MonomialCoefficient(Q, X*Y),
	MonomialCoefficient(Q, Y*Z)
	];

    II := ideal<Pa | LEQ>;
    vprint Reconstruction, 2 : "Ideal in the coefficients:", II;

    if Dimension(II) lt 0 then
	error "[DixmierOhnoToQuartic] Error: there is no B4 compatible with B8 and DO";
    end if;
    if Dimension(II) ne 0 then
	error "[DixmierOhnoToQuartic] Error: our current methods to determine b4 uniquely failed";
    end if;

    RD := RadicalDecomposition(II);
    vprint Reconstruction, 2 : "Ideal(s) in the coefficients:", RD;

    /*
    if #RD gt 1  then
	vprint Reconstruction, 2 : "Hum... let us investigate which one of these ideals is the good one", RD;
	for rd in RD do
	    GB := Basis(RD[1]);

	    NLEQ := GB;
	    for i in [ 74 .. 126 ] diff ( { 74, 79, 85, 86, 95, 96 } join { 75, 77, 78, 83, 84, 92, 93, 94 } ) do
		inv := JointInvariantFromDixmierOhno(QuadJointInvsNames[i], DO);
		COV,_Precomputations := JointCovariant(S8S4Cov, [B4,B8], QuadJointInvsIndices[i] : Precomputations :=_Precomputations);
		Append(~LEQ,Pa!(COV[1])-inv);
		Append(~NLEQ, )
	    end for;
	    j4
	end for;
    end if;
    */

    FQ := quo<Pa | RD[1]>;

    a0, a1, a2, a3, a4 := Explode(Random(Variety(RD[1], FQ)));
    return PolynomialRing(FQ)![a0, a1, a2, a3, a4];

end function;


intrinsic TernaryQuarticFromDixmierOhnoInvariants(DO::SeqEnum : exact := false, minimize := true, descent := true, search_point := true) -> RngMPolElt, SeqEnum
    {Reconstructs a ternary quartic from a given tuple of Dixmier-Ohno
    invariants DO.

    If the flag exact is set to true, then a ternary forms is returned whose
    Dixmier-Ohno invariants exactly equal DOInv (instead of merely being
    equal in the corresponding weighted projective space).
    
    If the flag descent is set to true, then the curve is descended to its base
    field.
    
    If the flag minimize is set to true, then over the rationals an effort is
    made to return as small a model as possible.
    
    If the flag search_point is set to true, then the algorithm tries to find a
    rational point of the Mestre conic of the associated binary form.}

    FF := Universe(DO);

    if Type(FF) eq RngInt then
	return
	   $$(ChangeUniverse(DO, Rationals()) : exact := exact, search_point := search_point);
    end if;

    P3 := PolynomialRing(FF, 3); X := P3.1; Y := P3.2; Z := P3.3;

    require
	(Characteristic(FF) eq 0) or (Characteristic(FF) gt 7)
	:
	"Characteristic must be 0 or > 7";

    require
	#DO eq 13 and DO[#DO] ne 0
	:
	"Only non singular curves (I27 <> 0) are currently handled";

    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27 := Explode(DO);
    twists := []; aut := <>;

    /*** Zero dimensional cases ***/

    /* C9 */
    if IsInStratumC9(DO) then
	vprintf Reconstruction, 1 : "Automorphism group C9\n";
	aut := SmallGroup(9, 1);
        twists := [X^3*Y + Y^3*Z + Z^4];
	return twists[1], aut, twists;
    end if;

    /* G48 */
    if IsInStratumG48(DO) then
	vprintf Reconstruction, 1 : "Automorphism group G48 \n";
	aut := SmallGroup(48, 33);
        twists := [X^4 + (Y^3 - Z^3)*Z];
	return twists[1], aut, twists;
    end if;

    /* G96 */
    if IsInStratumG96(DO) then
	vprintf Reconstruction, 1 : "Automorphism group G96 \n";
	aut := SmallGroup(96, 64);
        twists := [X^4 + Y^4 + Z^4];
	return twists[1], aut, twists;
    end if;

    /* G168 */
    if IsInStratumG168(DO) then
	vprintf Reconstruction, 1 : "Automorphism group G168 \n";
	aut := SmallGroup(168, 42);
	twists := [X^3*Y + Y^3*Z + Z^3*X];
	return twists[1], aut, twists;
    end if;

    /*** One dimensional cases ***/

    /* C6 */
    if IsInStratumC6(DO) then
	vprintf Reconstruction, 1 : "Automorphism group C6 \n";
	aut := SmallGroup(6, 2);
	if (12*I09^2+169*J18) ne 0 then
	    a :=
		6/5*(18*I09^2-51*I09*J09-9*J09^2+2888*I18-6342*J18)/(12*I09^2+169*J18);
	else
	    a := 18/5*(18*I09^2-51*I09*J09-9*J09^2-154*I18+756*J18)/(36*I09^2-169*I18);
	end if;

	twists := [ Z^3*Y+ a*X^4+a*X^2*Y^2+Y^4 ];
	return twists[1], aut, twists;
    end if;

    /* G16 */
    if IsInStratumG16(DO) then
	vprintf Reconstruction, 1 : "Automorphism group G16 \n";
	aut := SmallGroup(16, 13);
	a := -9/4*I03^3/I09;
	twists := [ X^4 + (Y^3 + a*Y*Z^2 + a*Z^3)*Z ];
	return twists[1], aut, twists;
    end if;

    /* S4 */
    if IsInStratumS4(DO) then
	vprintf Reconstruction, 1 : "Automorphism group S4 \n";
	aut := SmallGroup(24, 12);
	den := 120*I03^2*I06-61*I03*I09+23*I03*J09+1920*I06^2+300*I12;
	if den ne 0 then
	    a := -18/7*(840*I03^2*I06+53*I03*I09+I03*J09+13440*I06^2+660*I12-160*J12)/den;
	else
	    a := -6;
	end if;
	twists := [ X^4 + Y^4 + Z^4 + a*(X^2*Y^2 + Z^2*Y^2 + X^2*Z^2) ];
	return twists[1], aut, twists;
    end if;

    /*** Two dimensional cases ***/

    /* C3 */
    if IsInStratumC3(DO) then
	vprintf Reconstruction, 1 : "Automorphism group C3 \n";
	aut := SmallGroup(3, 1);
	twists := [
	    TernaryQuartic_C3(DO)
	    ];
	return twists[1], aut, twists;
    end if;

    /* D8 */
    if IsInStratumD8(DO) then
	vprintf Reconstruction, 1 : "Automorphism group D8 \n";
	aut := SmallGroup(8, 3);
	if I12 ne 0 then
	    twists := [
                TernaryQuarticFromDixmierOhnoInvariantsI12ne0(DO : exact := exact, minimize := minimize, descent := descent, search_point := search_point)
		];
	else
	    twists := [
		TernaryQuartic_D8_I12eq0(DO)
		];
	end if;
	return twists[1], aut, twists;
    end if;

    /* S3 */
    if IsInStratumS3(DO) then
	vprintf Reconstruction, 1 : "Automorphism group S3 \n";
	aut := SmallGroup(6, 1);
	if I12 ne 0 then
	    twists := [
                TernaryQuarticFromDixmierOhnoInvariantsI12ne0(DO : exact := exact, minimize := minimize, descent := descent, search_point := search_point)
		];
	else
	    twists := [
		TernaryQuartic_S3_I12eq0(DO)
		];
	end if;
	return twists[1], aut, twists;
    end if;

    /*** Three dimensional case ***/

    /* D4 */
    if IsInStratumD4(DO) then
	vprintf Reconstruction, 1 : "Automorphism group D4\n";
	aut := SmallGroup(4, 2);
	if I12 ne 0 then
	    twists := [
                TernaryQuarticFromDixmierOhnoInvariantsI12ne0(DO : exact := exact, minimize := minimize, descent := descent, search_point := search_point)
		];
	else
	    twists := [
		TernaryQuartic_D4_I12eq0(DO)
		];
	end if;
	return twists[1], aut, twists;
    end if;

    /*** Otherwise (C2 or <Id>) ***/
    if I12 ne 0 then
        twists := [
            TernaryQuarticFromDixmierOhnoInvariantsI12ne0(DO : exact := exact, minimize := minimize, descent := descent, search_point := search_point)
            ];
    end if;

    return twists[1], aut, twists;
end intrinsic;
