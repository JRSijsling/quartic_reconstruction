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
 *  Copyright 2016 R. Lercier, C. Ritzenthaler & J. Sijsling
 */

/* This code may fail in two places :

  _ in HyperellipticPolynomialFromJointShiodaInvariants, when the
    reconstructed octic has a (geom.) automorphism group equal to C14
    (to be checked, but it probably means that the quartic is singular)

  _ in DixmierOhnoToBinaryQuartic, when both the joint invariant constraints
    and the normalized contravariant constraints are not enough to get a fixed
    number of solutions. (but I never encoutered such a problem).

*/

import "DixmierOhnoInvariants.m": Rho, DixmierInvariant;
import "TernaryForms.m": TernaryToBinary, BinaryToTernary, Homogenization;
import "JointCovariants.dat": S8S4Cov;
import "JointCovariants.m": IthJointInvariant, JointCovariant;
import "Interpolations.m": JointInvariantFromDixmierOhno;

forward TernaryQuarticFromDixmierOhnoInvariants;
forward XGCDUnique;
forward HyperellipticPolynomialFromJointShiodaInvariants;
forward DixmierOhnoToJointShioda;
forward DixmierOhnoToBinaryQuartic;

declare verbose Reconstruction, 2;


intrinsic TernaryQuarticFromDixmierOhnoInvariants(DO::SeqEnum : exact := false) -> RngMPolElt, SeqEnum
    {Reconstructs a ternary quartic from a given tuple of Dixmier-Ohno
    invariants DO, and also returns the binary forms associated to it by the
    usual equivariant morphism.

    If the flag exact is set to true, then a ternary forms is returned whose
    Dixmier-Ohno invariants exactly equal DOInv (instead of merely being
    equal in the corresponding weighted projective space).}

    vprint Reconstruction : "Start of quartic reconstruction.";
    vprint Reconstruction : "Determining joint Shioda invariants from Dixmier-Ohno invariants...";
    JointShioda := DixmierOhnoToJointShioda(DO);
    vprint Reconstruction, 2 : "Joint Shioda invariants:", JointShioda;

    vprint Reconstruction : "Reconstructing binary octic b_8...";
    B8, lbd := HyperellipticPolynomialFromJointShiodaInvariants(JointShioda);
    if B8 eq 0 then
	error "[DixmierOhnoToQuartic] B8 has a root of order >= 4, not yet implemented";
    end if;
    vprint Reconstruction, 2 : "Reconstructed binary octic b_8:", lbd * Homogenization(B8 : degree := 8);

    vprint Reconstruction : "Reconstructing binary octic b_4...";
    B4 := DixmierOhnoToBinaryQuartic(DO, lbd*B8);
    vprint Reconstruction, 2 : "Reconstructed binary quartic b_4:", Homogenization(B4 : degree := 4);

    S := PolynomialRing(CoefficientRing(B4), 2);
    B8h := S ! Homogenization(B8 : degree := 8) * lbd;
    B4h := S ! Homogenization(B4 : degree := 4);
    B0h := S ! DO[3];
    vprint Reconstruction, 2 : "Reconstructed constant b_0:", B0h;

    vprint Reconstruction : "Final inversion...";
    F := Parent(DO[1]);
    // Get it to the base field if possible:
    if &and( &cat[ [ coeff in F : coeff in Coefficients(b) ] : b in [ B8h, B4h, B0h ] ] ) then
        R<x1, x2, x3> := PolynomialRing(F, 3);
    else
        R<x1, x2, x3> := PolynomialRing(BaseRing(Parent(B8h)), 3);
    end if;
    f := R ! BinaryToTernary([B8h, B4h, B0h]);
    if not exact then
        return f, [B8h, B4h, B0h];
    else
        //if DO[1] ne 0 then
        if false then
            // Save some time in generic case:
            lambda := DO[1]/DixmierInvariant(f, 3);
        else
            W := [ 3, 6, 9, 9, 12, 12, 15, 15, 18, 18, 21, 21, 27 ];
            indices := [ i : i in [1..#DO] | DO[i] ne 0 ];
            gcd, L := XGCDUnique([ W[i] : i in indices ]);
            I := DixmierOhnoInvariants(f);
            lambda := &*[ (DO[i] / I[i])^(L[i]) : i in indices ];
        end if;
        f := (1/lambda) * Evaluate(f, [ lambda*x1, x2, x3 ]);
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


function HyperellipticPolynomialFromJointShiodaInvariants(JS)

    s2, s3, s4, s5, s6, s7, s8, s9, s10 := Explode(JS);

    vprint Reconstruction : "Converting joint invariants to Shioda invariants...";
    /* Hard-coded the results of S8S4ToShioda.m */
    S2 := 40320*s2;
    S3 := 967680*s3;
    S4 := -(182476800*s4-276480000*s2^2);
    S5 := 20901888000*s5;
    S6 := -(-2483144294400*s6+39016857600*s3^2-1287556300800*s4*s2+1859803545600*s2^3);
    S7 := -(-466168955535360*s7-17657914982400*s4*s3+98322481152000*s5*s2+26754416640000*s3*s2^2);
    S8 := -(-419552059981824000*s8+29302048633651200/7*s4^2+337105649664000*s5*s3-6568744373452800*s6*s2-74950281422438400/7*s4*s2^2+46292784906240000/7*s2^4);
    S9 := -(-30904504418304000000*s9+495682899148800000*s5*s4-244650412081152000*s6*s3-9438958190592000*s3^3+1699352331839078400*s7*s2-276699527774208000*s4*s3*s2-1724275332218880000*s5*s2^2+441265944526848000*s3*s2^3);
    S10 := -(-131372369891827384320000/37*s10-54611115245568000000*s5^2-89184780750422016000*s6*s4-18795932287185715200*s7*s3-101709590298624000*s4*s3^2+704847460769464320000*s8*s2-22376109865697280000*s4^2*s2+3398024948613120000*s5*s3*s2+146163946229858304000*s6*s2^2+154105439846400000*s3^2*s2^2+63059945985146880000*s4*s2^3-44176892755968000000*s2^5);
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
    b8 := HyperellipticPolynomialFromShiodaInvariants([S2, S3, S4, S5, S6, S7, S8, S9, S10]);
    vprint Reconstruction, 2 : "Reconstructed non-twisted binary octic:", Homogenization(b8 : degree := 8);

    /* Extracting gcd of indices with non-zero invariant */
    Idx := [i : i in [1..9] | IsUnit(JS[i]) ];
    g, C := XGCDUnique([[2, 3, 4, 5, 6, 7, 8, 9, 10][i] : i in Idx]);

    /* Recalculate joint invariants to get exact values;
     * note that bs does not in general get all indices defined, only those in
     * Idx */
    bs := []; for i := 1 to #Idx do
	if C[i] ne 0 then
	    bs[Idx[i]] := Parent(s2)!IthJointInvariant(S8S4Cov, [0*b8, b8], Idx[i]);
	end if;
    end for;
    vprint Reconstruction, 2 : "Joint Shioda Invariants of b8:",
    [Parent(s2)!IthJointInvariant(S8S4Cov, [0*b8, b8], i) : i in [1..9]];

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
    vprint Reconstruction : "Twisting scalar:", Kl.1;
    return (PolynomialRing(Kl)!b8), Kl.1;

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


function DixmierOhnoToBinaryQuartic(DO, b8);

    LEQ := []; _Precomputations := [];
    I03,I06,I09,J09,I12,J12,I15,J15,I18,J18,I21,J21,I27 := Explode(DO);

    /* Coefficient ring plus deformation: */
    Pa<a0, a1, a2, a3, a4> := PolynomialRing(CoefficientRing(b8), 5);
    Pt := PolynomialRing(Pa); t := Pt.1;

    /* JRS: I trust you (so I have not changed anything) but I am a bit afraid
     * of using these rings because coercion occurs later */
    A0, A1, A2, A3, A4 := Explode([Pa.i : i in [1..5]]);
    B4 := Pt![A0, A1, A2, A3, A4];
    B8 := Pt!Coefficients(b8);

    /* We know proceed to use the invariants that give linear relations */
    vprint Reconstruction : "Trying with linear relations only...";

    LinearJointInvsNames := [ "j3", "j4c", "j5e", "j5f", "j6h", "j6i" ];
    LinearJointInvsIndices := [ 74, 79, 85, 86, 95, 96 ];

    for i:=1 to #LinearJointInvsNames do
        inv := JointInvariantFromDixmierOhno(LinearJointInvsNames[i], DO);
        COV,_Precomputations := JointCovariant(S8S4Cov, [B4,B8], LinearJointInvsIndices[i] : Precomputations :=_Precomputations);
        Append(~LEQ,Pa!(COV[1])-inv);
    end for;

    vprint Reconstruction : "Linear constraints :", LEQ;
    II := ideal<Pa | LEQ>;

    /* Generic case */
    if Dimension(II) lt 0 then
	error "[DixmierOhnoToQuartic] Error: there is no B4 compatible with B8 and DO";
    end if;
    if Dimension(II) eq 0 then
	V := Variety(II);
	if #V eq 1 then
	    a0, a1, a2, a3, a4 := Explode(Random(Variety(II)));
            vprint Reconstruction : "Linear relations suffice.";
	    return Parent(b8)![a0, a1, a2, a3, a4];
	end if;
    end if;

    /* Strange situation, we try to add degree 2 constraints */
    vprint Reconstruction : "Adding more, non-linear, constraints...";

    QuadJointInvsNames := [ "j3a", "j4a", "j4b", "j5c", "j5d", "j6e", "j6f", "j6g" ];
    QuadJointInvsIndices := [ 75, 77, 78, 83, 84, 92, 93, 94 ];

    for i:=1 to #QuadJointInvsNames do
        inv := JointInvariantFromDixmierOhno(QuadJointInvsNames[i], DO);
        COV,_Precomputations := JointCovariant(S8S4Cov, [B4,B8], QuadJointInvsIndices[i] : Precomputations :=_Precomputations);
        Append(~LEQ,Pa!(COV[1])-inv);
    end for;

    /* In case we fail, we try to add more (but non-linear) constraints, which
     * impose that the covariant of the end result is normalized */
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

    FQ := quo<Pa | RD[1]>;

    a0, a1, a2, a3, a4 := Explode(Random(Variety(RD[1], FQ)));
    return PolynomialRing(FQ)![a0, a1, a2, a3, a4];

end function;
