/***
 *  Joint invariants of Sym^4 x Sym^8
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

/* Usage:
 * FdCov is record of fundamental covariants, typically S8S4Cov after loading JointCovariants.dat.
 * JointCovariant(S8S4Cov, [g, f], n) then returns the nth joint covariant
 * AllJointInvariants(S8S4Cov, [g, f]) returns all joint invariants along with their weights.
 * FirstJointInvariants(S8S4Cov, [g, f], n) returns the first n joint invariants.
 * IthJointInvariant(S8S4Cov, [g, f], n) returns the nth joint invariant.
 *
 * GetJointCovariant does not seem to be used for now.
 */

import "TernaryForms.m": Homogenization, Dehomogenization;
import "JointCovariants.dat": S8S4Cov;

/* A covariant (U, V)^level */
COV_t :=  recformat<
    U, 			// Covariants in U
    V, 			// Covariants in V
    level,		// Transvectant order
    degree,             // Covariant degree
    order               // Covariant order
    >;

function UnivariateTransvectant(F, G, r)

    Q, Qdeg, n := Explode(F);
    R, Rdeg, m := Explode(G);

    n := IntegerRing()!n;
    m := IntegerRing()!m;

    K := BaseRing(Parent(Q));

    h := Parent(Q)!0;
    for k := 0 to r do
	h +:= (-1)^k
	    * Binomial(m-k,r-k)  * Derivative(Q, r-k)
	    * Binomial(n-r+k, k) * Derivative(R, k);
    end for;

    coef := Factorial(m-r)*Factorial(n-r)/Factorial(m)/Factorial(n);
    h := (K!coef) * h;

    return [* h, Qdeg+Rdeg, n+m-2*r *];

end function;


forward JointCovariant;
function JointCovariant(FdCov, forms, idx : Precomputations := [])

    // JRS: This does not work yet and I have dropped it for now
    //if #GeneratorsSequence(Parent(forms[1])) ne 1 then
    //    Cov, Precomputations := JointCovariant(FdCov, [ Dehomogenization(form) : form in forms ], idx);
    //    return [ Homogenization(cov) : cov in Cov ], Precomputations;
    //end if;

    if IsDefined(Precomputations, 1+idx) then
	return Precomputations[1+idx], Precomputations;
    end if;

    _Precomputations := Precomputations;
    Cov := FdCov[1+idx];

    /* Is Cov equal to a product of the initial forms ? */
    if  (Cov`U meet {* i : i in [0..#forms-1] *}) eq Cov`U  and Cov`V eq {* *} then
	_Precomputations[1+idx] := [*
	    &*[forms[1+i] : i in Cov`U],
	    &+[FdCov[i+1]`degree : i in Cov`U],
	    &+[FdCov[i+1]`order : i in Cov`U]
	    *];
	return _Precomputations[1+idx], _Precomputations;
    end if;

    if  (Cov`V meet {* i : i in [0..#forms-1] *}) eq Cov`V  and Cov`U eq {* *} then
	_Precomputations[1+idx] := [*
	    &*[forms[1+i] : i in Cov`V],
	    &+[FdCov[i+1]`degree : i in Cov`V],
	    &+[FdCov[i+1]`order : i in Cov`V]
	    *];
	return _Precomputations[1+idx], _Precomputations;
    end if;

    /* First, let us obtain the covariant U_cov */
    U_cov := Universe(forms)!1; U_deg := 0; U_ord := 0;
    for cov_idx in MultisetToSet(Cov`U) do

	COV, _Precomputations := JointCovariant(FdCov, forms, cov_idx : Precomputations := _Precomputations);
	cov, _ := Explode(COV);

	U_cov *:= cov ^ Multiplicity(Cov`U, cov_idx);
	U_deg +:= FdCov[cov_idx+1]`degree * Multiplicity(Cov`U, cov_idx);
	U_ord +:= FdCov[cov_idx+1]`order * Multiplicity(Cov`U, cov_idx);

    end for;

    /* Then, let us obtain the covariant V_cov */
    V_cov := Universe(forms)!1; V_deg := 0; V_ord := 0;
    for cov_idx in MultisetToSet(Cov`V) do

	COV, _Precomputations := JointCovariant(FdCov, forms, cov_idx : Precomputations := _Precomputations);
	cov, _ := Explode(COV);

	V_cov *:= cov ^ Multiplicity(Cov`V, cov_idx);
	V_deg +:= FdCov[cov_idx+1]`degree * Multiplicity(Cov`V, cov_idx);
	V_ord +:= FdCov[cov_idx+1]`order * Multiplicity(Cov`V, cov_idx);

    end for;

    /* Output the transvectant */
    _Precomputations[1+idx] := UnivariateTransvectant([U_cov, U_deg, U_ord], [V_cov, V_deg, V_ord], Cov`level);
    return _Precomputations[1+idx], _Precomputations;

end function;


function AllJointInvariants(FdCov, forms)

    LInv := []; LDeg := [];

    _Precomputations := [];
    for i := 0 to #FdCov-1 do
	if FdCov[1+i]`order eq 0 then
	    COV, _Precomputations := JointCovariant(FdCov, forms, i : Precomputations := _Precomputations);
	    Append(~LInv, COV[1]); Append(~LDeg, Integers()!COV[2]);
	end if;
    end for;

    return LInv, LDeg;
end function;


forward GetJointCovariant;
function GetJointCovariant(FdCov, forms, Cov)

    /* Is Cov equal to a product of the initial forms ? */
    if  (Cov`U meet {* i : i in [0..#forms-1] *}) eq Cov`U  and Cov`V eq {* *} then
	return [
	    &*[forms[1+i] : i in Cov`U],
	    &+[FdCov[i+1]`degree : i in Cov`U],
	    &+[FdCov[i+1]`order : i in Cov`U]
	    ];
    end if;

    if  (Cov`V meet {* i : i in [0..#forms-1] *}) eq Cov`V  and Cov`U eq {* *} then
	return [
	    &*[forms[1+i] : i in Cov`V],
	    &+[FdCov[i+1]`degree : i in Cov`V],
	    &+[FdCov[i+1]`order : i in Cov`V]
	    ];
    end if;

    _Precomputations := [];

    /* First, let us obtain the covariant U_cov */
    U_cov := Universe(forms)!1; U_deg := 0; U_ord := 0;
    for cov_idx in MultisetToSet(Cov`U) do

	COV, _Precomputations := JointCovariant(FdCov, forms, cov_idx : Precomputations := _Precomputations);
	cov, _ := Explode(COV);

	U_cov *:= cov ^ Multiplicity(Cov`U, cov_idx);
	U_deg +:= FdCov[cov_idx+1]`degree * Multiplicity(Cov`U, cov_idx);
	U_ord +:= FdCov[cov_idx+1]`order * Multiplicity(Cov`U, cov_idx);

    end for;

    /* Then, let us obtain the covariant V_cov */
    V_cov := Universe(forms)!1; V_deg := 0; V_ord := 0;
    for cov_idx in MultisetToSet(Cov`V) do

	COV, _Precomputations := JointCovariant(FdCov, forms, cov_idx : Precomputations := _Precomputations);
	cov, _ := Explode(COV);

	V_cov *:= cov ^ Multiplicity(Cov`V, cov_idx);
	V_deg +:= FdCov[cov_idx+1]`degree * Multiplicity(Cov`V, cov_idx);
	V_ord +:= FdCov[cov_idx+1]`order * Multiplicity(Cov`V, cov_idx);

    end for;

    delete _Precomputations;

    /* Output the transvectant */
    return UnivariateTransvectant([U_cov, U_deg, U_ord], [V_cov, V_deg, V_ord], Cov`level);

end function;


function FirstJointInvariants(FdCov, forms, nb)

    LInv := []; LDeg := [];

    _Precomputations := [];
    for i := 0 to #FdCov-1 do
	if FdCov[1+i]`order eq 0 then
	    COV, _Precomputations := JointCovariant(FdCov, forms, i :
		Precomputations := _Precomputations);
	    Append(~LInv, COV[1]); Append(~LDeg, Integers()!COV[2]);
	end if;
	if #LInv eq nb then break; end if;
    end for;

    return LInv, LDeg;
end function;


function IthJointInvariant(FdCov, forms, idx)

    jdx := 0;  Inv := Universe(forms)!0; Deg := 0;
    for i := 0 to #FdCov-1 do
	if FdCov[1+i]`order eq 0 then
	    jdx +:= 1;
	    if jdx eq idx then
		COV, Prc := JointCovariant(FdCov, forms, i);
		delete Prc;
		Inv := COV[1]; Deg := Integers()!COV[2];
		break i;
	    end if;
	end if;
    end for;

    return Inv, Deg;
end function;


intrinsic JointShiodaInvariants(f :: RngMPolElt) -> SeqEnum
    {Calculates the joint Shioda invariants of an octic polynomial f.}
    
    return FirstJointInvariants(S8S4Cov, [0, f], 9), [2..10];
end intrinsic;


intrinsic ShiodaInvariantsFromJointShiodaInvariants(JS :: SeqEnum) -> SeqEnum
    {Converts joint Shioda invariants to Shioda invariants.}

    s2, s3, s4, s5, s6, s7, s8, s9, s10 := Explode(JS);

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
    return [S2, S3, S4, S5, S6, S7, S8, S9, S10];

end intrinsic;
