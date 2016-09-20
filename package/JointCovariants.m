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


function JointShiodaInvariants(f);

return FirstJointInvariants(S8S4Cov, [0, f], 9), [2..10];

end function;
