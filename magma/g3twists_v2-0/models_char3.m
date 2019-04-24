//freeze;

/***
 *  Reconstruction algorithm for genus 3 hyperelliptic curve with non-trivial
 *  automorphism groups defined over a field of characteristic 3 from their invariants
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
 *  Copyright 2013, R. Basson & R. Lercier & C. Ritzenthaler
 */


import "g3d4_char3.m"            : G3Char3Models_D2;
import "conic_char3.m"           : Genus3Char3ConicAndQuartic, Genus3Char3ConicAndQuarticForC4;
import "hilbert90.m"             : MConj, MNorm, MActOnC, Glasby;


/*************** Some useful quartics ***************/

 function InvariantsQuarticChar3(f : normalize:= true)

     a0:= Coefficient(f, 0); a1:= Coefficient(f, 1);
     a2:= Coefficient(f, 2); a3:= Coefficient(f, 3);
     a4:= Coefficient(f, 4);

     I:= a2;
     J:= a0^3*a4^3 + a0^2*a2^2*a4^2 + a0*a1*a2^2*a3*a4 + a0*a2^4*a4 + 2*a0*a2^3*a3^2 + 2*a1^3*a3^3 + 2*a1^2*a2^3*a4 + a1^2*a2^2*a3^2;

     Wght:= [1, 6];

     if normalize eq false then return [I, J], Wght; end if;
     return WPSNormalize(Wght, [I, J]), Wght;

 end function;


 function QuarticCovChar3(f, numero)

     a0:= Coefficient(f, 0); a1:= Coefficient(f, 1);
     a2:= Coefficient(f, 2); a3:= Coefficient(f, 3);
     a4:= Coefficient(f, 4); a5:= Coefficient(f, 5);
     a6:= Coefficient(f, 6); a7:= Coefficient(f, 7);
     a8:= Coefficient(f, 8);

     x:= Parent(f).1;

     if numero eq 1 then
	 return (a5^2 + 2*a2*a8)*x^4 + (2*a4*a5 + 2*a2*a7 + 2*a1*a8)*x^3 +
		(a4^2 + 2*a3*a5 + 2*a2*a6 + 2*a1*a7 + 2*a0*a8)*x^2 +
		(2*a3*a4 + 2*a1*a6 + 2*a0*a7)*x +
		a3^2 + 2*a0*a6;
     elif numero eq 2 then
	 return (2*a4^2*a6 + a3*a5*a6 + a2*a6^2 + a3*a4*a7 + a2*a5*a7 + 2*a1*a6*a7 + a0*a7^2 + 2*a3^2*a8 + a2*a4*a8 + a1*a5*a8 + 2*a0*a6*a8)*x^4
		+ (2*a3*a4*a6 + 2*a2*a5*a6 + 2*a1*a6^2 + a3^2*a7 + 2*a2*a4*a7 + 2*a1*a5*a7 + a0*a6*a7 + 2*a2*a3*a8 + 2*a1*a4*a8 + 2*a0*a5*a8)*x^3
		+ (2*a2*a4*a5 + a1*a5^2 + 2*a2*a3*a6 + 2*a1*a4*a6 + 2*a0*a5*a6 + 2*a2^2*a7 + 2*a1*a3*a7 + 2*a0*a4*a7 + a1*a2*a8 + 2*a0*a3*a8)*x
		+ 2*a2*a4^2 + a2*a3*a5 + a1*a4*a5 + 2*a0*a5^2 + a2^2*a6 + a1*a3*a6 + a0*a4*a6 + 2*a1*a2*a7 + a0*a3*a7 + a1^2*a8 + 2*a0*a2*a8;
     else
	 return  (2*a4^2*a5^2 + a3*a5^3 + a4^3*a6 + 2*a2*a5^2*a6 + 2*a2*a4*a6^2 + a1*a5*a6^2 +
		  2*a3*a4^2*a7 + 2*a3^2*a5*a7 + 2*a2*a4*a5*a7 + a2*a3*a6*a7 + 2*a1*a4*a6*a7 +
		  a1*a3*a7^2 + a3^2*a4*a8 + 2*a2*a3*a5*a8 + a2^2*a6*a8 + 2*a1*a3*a6*a8 +
		  a1*a2*a7*a8 + a1^2*a8^2)*x^4
		 + (a4^3*a5 + 2*a3*a4*a5^2 + a3*a4^2*a6 + a3^2*a5*a6 + 2*a2*a4*a5*a6 + 2*a1*a5^2*a6 +
		    a1*a4*a6^2 + 2*a0*a5*a6^2 + 2*a3^2*a4*a7 + 2*a2*a4^2*a7 + 2*a1*a4*a5*a7 + a2^2*a6*a7 +
		    2*a1*a3*a6*a7 + a0*a4*a6*a7 + a1*a2*a7^2 + 2*a0*a3*a7^2 + 2*a3^3*a8 + 2*a2*a3*a4*a8 +
		    2*a1*a3*a5*a8 + a1*a2*a6*a8 + a0*a3*a6*a8 + 2*a0*a2*a7*a8 + a0*a1*a8^2)*x^3
		 + (2*a4^4 + 2*a3*a4^2*a5 + 2*a3^2*a5^2 + 2*a2*a3*a5*a6 + 2*a1*a4*a5*a6 +
		    2*a0*a5^2*a6 + a2^2*a6^2 + 2*a2*a3*a4*a7 + 2*a1*a4^2*a7 + 2*a0*a4*a5*a7 +
		    2*a1*a2*a6*a7 + 2*a1^2*a7^2 + 2*a0*a2*a7^2 + 2*a2*a3^2*a8 + 2*a1*a3*a4*a8 +
		    2*a0*a3*a5*a8 + 2*a1^2*a6*a8 + 2*a0*a1*a7*a8 + a0^2*a8^2)*x^2
		 + (a3*a4^3 + 2*a3^2*a4*a5 + a2*a4^2*a5 + a2*a3*a5^2 + 2*a1*a4*a5^2 + 2*a0*a5^3 +
		    2*a2*a3*a4*a6 + 2*a1*a4^2*a6 + 2*a0*a4*a5*a6 + a1*a2*a6^2 + 2*a2*a3^2*a7 +
		    a2^2*a4*a7 + 2*a1*a3*a4*a7 + 2*a1*a2*a5*a7 + 2*a0*a3*a5*a7 + a1^2*a6*a7 +
		    a0*a2*a6*a7 + 2*a2^2*a3*a8 + a1*a2*a4*a8 + 2*a1^2*a5*a8 + a0*a2*a5*a8 +
		    2*a0*a1*a6*a8 + a0^2*a7*a8)*x
		 + 2*a3^2*a4^2 + a2*a4^3 + a3^3*a5 + 2*a1*a4^2*a5 + 2*a1*a3*a5^2 + a0*a4*a5^2 +
		 2*a2*a3^2*a6 + 2*a2^2*a4*a6 + 2*a1*a3*a4*a6 + a1*a2*a5*a6 + 2*a0*a3*a5*a6 +
		 a0*a2*a6^2 + a2^2*a3*a7 + 2*a1*a2*a4*a7 + a1^2*a5*a7 + 2*a0*a2*a5*a7 + a0*a1*a6*a7 + a0^2*a7^2;
     end if;

 end function;

/*************** Reconstruction ***************/

/* Case V8 :
     y^2 = x^8 - 1,
     see [MaShShVo2002].
*/
function G3Char3Models_G32_9(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;
    f:= x^8 - 1;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;


/* Case C14 :
     y^2 = x^7 - 1,
     see [MaShShVo2002].
*/
function G3Char3Models_C14(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;
    f:= x^7 - 1;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;


/* Case C2xD4 :
     y^2 = x^8 + a*x^4 + b,
     J2 = 0 or J5*J3 + J3^2*J2 + J4*J2^2 + 2*J2^4 = 0 (Discrim = 0),
     see [MaShShVo2002].
*/
function G3Char3Models_C2xD4(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;
    J2, J3, J4, J5, J6, J7, J8:= Explode(JI);

    if J3 eq 0 and J4 eq 0 then
	error "[models_char3] G32_9 case trapped in G3Char3Models_GC2xD4 by error at JI = ", JI;
    elif J2 eq 0 then
	/* error "[models_char3] singular case in G3Char3Models_GC2xD4 at JI = ", JI; */
	Pa:= x^3 + J3;
	if not IsIrreducible(Pa) then
	    a:= [r[1] : r in Roots(Pa)][1];
	    b:= a^2;
	else
	    if not IsFinite(FF) then
		K3:= quo<Parent(x) | Pa>;
		a:= K3.1; x:= PolynomialRing(K3).1;
		b:= a^2;
	    else
		K3:= ExtensionField<FF, x | Pa>;
		a:= K3.1; x:= PolynomialRing(K3).1;
		b:= a^2;
	    end if;
	end if;
    else
	a:= (2*J2*J3 + J5)/J2^2;
	b:= J2 + a^2;
    end if;

    f:= x^8 + a*x^4 + b;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;


/* Case C2xC4 :
     y^2 = a^2*x^8 + 2*a^2*x^6 + 2*a*x^2 +2,
     J6 + J4*J2 + J2^3 = 0 ou J4 + 2*J2^2 = 0 (Discrim = 0),
     see [MaShShVo2002].
*/
function G3Char3Models_C2xC4(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;
    J2, J3, J4, J5, J6:= Explode(JI);

    if J6 eq 0 then
	error "[models_char3] G32_9 case trapped in G3Char3Models_C2xC4 by error at JI = ", JI;
    elif J4 eq 0 then /* singular case */
	return [x^7 + x^5 + 2*x^3 + 2*x];
    elif J2^2+2*J4 eq 0 then /* singular case */
	return [(x^2-1)*(x^2+1)^3];
    else
	a:= J2/(J4*J2^2 + 2*J4^2)*J6 + 2*J4/(J2^2 + 2*J4);
    end if;

    f:= a^2*x^8 + a^2*x^6 + a*x^2 + 2;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;


/* Case C2^3 :
     y^2 = a0*x^8 + a2*x^6 + a4*x^4 + a2*x^2 + a0,
     J2^3 + 2*J3^2 + J2*J4 + J6 = J2^4*J4 + 2*J2*J3^2*J4 + J2^2*J4^2 + J4^3 + 2*J2^2*J3*J5 + J3*J4*J5 = 0 (Discrim = 0),
     see [MaShShVo2002].
*/

function G3Char3Models_C2x3(JI : geometric:= false, descent:= true)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;
    J2, J3, J4, J5, J6, J7:= Explode(JI);

    /* Case where the automorphism group is larger (C2xD4). */
    if 2*J3^2 + 2*J2*J4 + J6 eq 0 then
	error "[models_char3] G_C2xD4 case trapped in G3Char3Models_C2x3 by error at JI = ", JI;
    end if;

    if J3 eq 0 then

	if J6 eq 0 then error "[models_char3] G32_9 case trapped in G3Char3Models_C2x3 by error at JI = ", JI; end if;
	if J4 eq 0 then error "[models_char3] C2xC4 case trapped in G3Char3Models_C2x3 by error at JI = ", JI; end if;

	a4:= 0;
	nu:= 2*J2/(J4^3*J2^2 + 2*J4^4)*J5^3 + (J2^4 + J4^2)/(J4^2*J2^2 + 2*J4^3)*J5;
	a6:= 2*nu^2 + J2;
	a8:= a6*nu;
	if a6 eq 0 then
	    error "[models_char3] C2xD4 case trapped in G3Char3Models_C2x3 by error at JI = ", JI;
	end if;
	l:= 1/a6;
	f:= a8*x^8 + a6*x^6 + a4*x^4 + l*a6*x^2 + l^2*a8;
	if geometric then return [f]; end if;
	return HyperellipticPolynomialTwists(f, 8);

    else /* J3 <> 0, i.e. a4 <> 0, because 2*J3^2 + 2*J2*J4 + J6 <> 0 */

	Pa4:= (2*J3^2 + 2*J2*J4 + J6)*x^3 +
	      (2*J2*J5 + 2*J7)*x^2 +
	      (2*J2*J3^2 + 2*J2^2*J4 + 2*J4^2 + 2*J3*J5 + 2*J2*J6)*x +
	      2*J3^3 + 2*J2*J3*J4 + J3*J6;

	if not IsIrreducible(Pa4) then
	    /* Easy, we may find a rational model in this case	 */
	    a4:= [r[1] : r in Roots(Pa4)][1];
	    a6:= 2*(a4^3+a4*J2+J3)/a4;
	    if a6 eq 0 or J4^2 + a4*J2*J5 + J3*J5 + 2*J2*J6 + a4*J7 eq 0 then
		error "[models_char3] C2xD4 case trapped in G3Char3Models_C2x3 by error at JI = ", JI;
	    end if;
	    a8:= 2*a6^2*(a4*J3^2 + a4*J2*J4 + J2*J5 + 2*a4*J6 + J7)/(J4^2 + a4*J2*J5 + J3*J5 + 2*J2*J6 + a4*J7);
	    l:= 1/a6;
	    f:= a8*x^8 + a6*x^6 + a4*x^4 + l*a6*x^2 + l^2*a8;
	    if geometric then return [f]; end if;
	    return HyperellipticPolynomialTwists(f, 8);

	else /* Let's go in a degree 3 extension */

	   Pa4 /:= Coefficient(Pa4, Degree(Pa4));
	   if IsFinite(FF) then K3:= ext<FF | Pa4>; else K3:= quo<Parent(x) | Pa4>; end if;
	   a4:= K3.1; x:= PolynomialRing(K3).1;
	   a6:= 2*(a4^3+a4*J2+J3)/a4;
	   if a6 eq 0 or J4^2 + a4*J2*J5 + J3*J5 + 2*J2*J6 + a4*J7 eq 0 then
	       error "[models_char3] C2xD4 case trapped in G3Char3Models_C2x3 by error at JI = ", JI;
	   end if;
	   a8:= 2*a6^2*(a4*J3^2 + a4*J2*J4 + J2*J5 + 2*a4*J6 + J7)/(J4^2 + a4*J2*J5 + J3*J5 + 2*J2*J6 + a4*J7);
	   l:= 1/a6;

	   fK3:= a8*x^8 + a6*x^6 + a4*x^4 + l*a6*x^2 + l^2*a8;

	   /* if Discriminant(fK3) eq 0 then return [fK3]; end if; */

	   /* Descent on FF with covariant method */
	   if descent then
	       CK3:= QuarticCovChar3(fK3, 1); JCK3:= InvariantsQuarticChar3(CK3 : normalize:= true);
	       if JCK3[1] eq 0 or JCK3[2] eq 0 then CK3:= QuarticCovChar3(fK3, 2); JCK3:= InvariantsQuarticChar3(CK3 : normalize:= true); end if;
	       if JCK3[1] eq 0 or JCK3[2] eq 0 then CK3:= QuarticCovChar3(fK3, 3); JCK3:= InvariantsQuarticChar3(CK3 : normalize:= true); end if;
	       if JCK3[1] eq 0 or JCK3[2] eq 0 then
		   error "[models_char3] C2xD4 case trapped in G3Char3Models_C2x3 by error at JI = ", JI;
	       end if;

	       if IsEmpty(Roots(CK3)) then
		   fact:= Factorisation(CK3)[1,1];
		   if IsFinite(FF) then KC:= ext<K3 | fact>;
		   else KC:= quo<Parent(x) | fact>; end if;
		   x:= PolynomialRing(KC).1;
	       end if;

	       k2:= x^3 + JCK3[1]*x^2 + 2*JCK3[2]/JCK3[1]^3;

	       ret, ML:= IsGL2Equivalent(Parent(x)!CK3, k2, 4);

	       f:= MActOnC(Parent(x)!fK3, 8, Matrix(2, 2, ML[1]));
	       f:= f/LeadingCoefficient(f);
	       f:= PolynomialRing(FF)!Eltseq(f);
           else
	       f:= fK3;
 	   end if;
	   if geometric then return [f]; end if;
	   return HyperellipticPolynomialTwists(f, 8);

	end if;
    end if;

end function;







function G3Char3Models(JI: geometric:= true, models:= true, descent:= true)

    FF:= Universe(JI);
    J2, J3, J4, J5, J6, J7, J8, J9, J10, J12:= Explode(JI);
    twists:= [];

    /* Point at infinity */
    if J2 eq 0 and J3 eq 0 and
       J4 eq 0 and J5 eq 0 and
       J6 eq 0 and J7 eq 0 and
       J8 eq 0 and J9 eq 0 and
       J10 eq 0 and J12 eq 0 then
	vprintf G3Twists, 1 : "Automorphism group VIII, curve y^2 = x^8\n";
	aut:= SmallGroup(1,1);/* FixMe: <1,1> is not the good choice here */
	if models then twists:= [(PolynomialRing(FF).1)^8]; end if;
	if geometric or not models then return twists, aut; end if;
	error "[models_char3] no possible twist computations for singular forms, sorry";
	return [], <>;
    end if;



     /*** Zero dimensional cases ***/

     /* V8 : y^2 = x^8 - 1  */
     if J3 eq 0 and J4 eq 0 and J5 eq 0 and J6 eq 0 and J7 eq 0
	and J8-J2^4 eq 0 and J9 eq 0 and J10-J2^5 eq 0 and 2*J12-J2^6 eq 0 then
	 vprintf G3Twists, 1 : "Automorphism group V8, curve y^2 =  x^8 - 1\n";
	 aut:= SmallGroup(32, 9);
	 if models then twists:= G3Char3Models_G32_9(JI : geometric:= geometric); end if;
	 return twists, aut;
     end if;


     /* C14 : y^2 = x^7 - 1 */
     if J2 eq 0 and J3 eq 0 and J4 eq 0 and J5 eq 0 and J6 eq 0
	and J8 eq 0 and J9 eq 0 and J10 eq 0 and J12 eq 0 then
	 vprintf G3Twists, 1 : "Automorphism group C14, curve y^2 = x^7 - 1\n";
	 aut:= CyclicGroup(14); /* SmallGroup(14, 2) */
	 if models then twists:= G3Char3Models_C14(JI : geometric:= geometric); end if;
	 return twists, aut;
     end if;


     /*** One dimensional cases ***/

     /* C2 x D4 : y^2 = x^8 + a*x^4 + 1 or a*x^8 + a*x^4 + b*/
     if J12 + J3^4 + 2*J5*J3*J2^2 + 2*J3^2*J2^3 + J4*J2^4 + J2^6 eq 0 and
	J10 + J4*J2^3 + 2*J2^5 eq 0 and
	J5^2 + J5*J3*J2 + J3^2*J2^2 + J4*J2^3 eq 0 and
	J9 + 2*J4*J3*J2 + 2*J5*J2^2 + 2*J3*J2^3 eq 0 and
	J5*J4 + 2*J4*J3*J2 + 2*J5*J2^2 eq 0 and
	J8 + J5*J3 + J4*J2^2 + 2*J2^4 eq 0 and
	J4^2 + J5*J3 + 2*J3^2*J2 + 2*J4*J2^2 eq 0 and
	J7 + J5*J2 eq 0 and
	J6 + 2*J3^2 + 2*J4*J2 eq 0
	then
	 vprintf G3Twists, 1 : "Automorphism group C2xD4, curve y^2 = x^8 + a*x^4 + 1\n";
	 aut:= SmallGroup(16, 11);
	 if models then twists:= G3Char3Models_C2xD4(JI : geometric:= geometric); end if;
	 return twists, aut;
     end if;

     /* C2 x C4 : y^2 = x * (x^2 - 1) * (x^4 + a * x^2 + 1) */
     if J3 eq 0 and J5 eq 0 and J7 eq 0 and J9 eq 0 and
	J12 + J4^3 + 2*J4^2*J2^2 + J4*J2^4 + J2^6 eq 0 and
	J6^2 + J4^3 + J6*J2^3 eq 0 and
	J10 + J4^2*J2 + 2*J6*J2^2 + 2*J2^5 eq 0 and
	J8 + 2*J4^2 + J4*J2^2 + 2*J2^4 eq 0
	then
	 vprintf G3Twists, 1 : "Automorphism group C2xC4, curve y^2 = x * (x^2 - 1) * (x^4 + a * x^2 + 1)\n";
	 aut:= DirectProduct(CyclicGroup(2), CyclicGroup(4));	/* SmallGroup(8, 2) */
	 if models then twists:= G3Char3Models_C2xC4(JI : geometric:= geometric); end if;
	 return twists, aut;
     end if;


     /*** Two dimensional cases ***/

     /* C2^3 : y^2 = a8*x^8 + a6*x^6 + a4*x^4 + a6*x^2 + a8 */
     if  J7^2 + 2*J6*J4^2 + J7*J4*J3 + J4^2*J3^2 + 2*J4^3*J2 + J5*J4*J3*J2 + J6*J3^2*J2 + 2*J3^4*J2 + J6*J4*J2^2 +
         J4*J3^2*J2^2 + 2*J4^2*J2^3 eq 0 and
	 J7*J6 + 2*J5*J4^2 + J6*J4*J3 + 2*J7*J3^2 + 2*J4*J3^3 + J7*J4*J2 + J4^2*J3*J2 + J5*J3^2*J2 + 2*J5*J4*J2^2 +
         2*J6*J3*J2^2 + J4*J3*J2^3 + J5*J2^4 eq 0 and
	 J12 + 2*J5*J4*J3 + J3^4 + J6*J4*J2 + 2*J7*J3*J2 + 2*J4^2*J2^2 + 2*J5*J3*J2^2 + 2*J3^2*J2^3 + J4*J2^4 + J2^6 eq 0 and
	 J6^2 + J4^3 + J5*J4*J3 + J6*J3^2 + J3^4 + J7*J3*J2 + 2*J4*J3^2*J2 + J6*J2^3 eq 0 and
	 J7*J5 + J4^3 + J5*J4*J3 + J6*J4*J2 + J4*J3^2*J2 + J5*J3*J2^2 eq 0 and
	 J6*J5 + J7*J4 + 2*J5*J3^2 + 2*J5*J4*J2 + J4*J3*J2^2 + J5*J2^3 eq 0 and
	 J10 + 2*J6*J4 + J7*J3 + J4*J3^2 + 2*J6*J2^2 + 2*J3^2*J2^2 + 2*J2^5 eq 0 and
	 J5^2 + J6*J4 + 2*J4*J3^2 + 2*J5*J3*J2 eq 0 and
	 J9 + J5*J4 + J7*J2 + J4*J3*J2 + 2*J5*J2^2 + 2*J3*J2^3 eq 0 and
	 J8 + J5*J3 + J4*J2^2 + 2*J2^4 eq 0
	 then
	 vprintf G3Twists, 1 : "Automorphism group C2xC2xC2, curve y^2 = a8*x^8 + a6*x^6 + a4*x^4 + a6*x^2 + a8\n";
	 aut:= SmallGroup(8, 5);
	 if models then twists:= G3Char3Models_C2x3(JI : geometric:= geometric, descent:= descent); end if;
	 return twists, aut;
     end if;



     /* C4 : y^2 = x*(x^2-1)*(x^4+a*x^2+b)  */
     if J3 eq 0 and J5 eq 0 and J7 eq 0 and J9 eq 0 and
	J12^2 + J8^3 + J8^2*J4^2 + 2*J12*J4^3 + J8*J4^4 + J4^6 + 2*J8^2*J6*J2 + 2*J12*J6*J4*J2 + 2*J8*J6*J4^2*J2 +
        J10*J4^3*J2 + J6*J4^4*J2 + 2*J12*J8*J2^2 + J8^2*J4*J2^2 + J12*J4^2*J2^2 + J8*J6*J4*J2^3 +
        2*J10*J4^2*J2^3 + 2*J6*J4^3*J2^3 + 2*J8*J6*J2^5 + 2*J4^3*J2^6 + J6*J4*J2^7 + 2*J8*J2^8 + 2*J6*J2^9 +
        2*J4*J2^10 + J2^12 eq 0 and
	J12*J10 + J8^2*J6 + J8*J6*J4^2 + J10*J4^3 + J6*J4^4 + 2*J12*J8*J2 + 2*J8^2*J4*J2 + 2*J12*J4^2*J2 +
        J8*J4^3*J2 + J4^5*J2 + 2*J12*J6*J2^2 + 2*J8*J6*J4*J2^2 + 2*J10*J4^2*J2^2 + 2*J12*J4*J2^3 +
        2*J8*J4^2*J2^3 + 2*J4^4*J2^3 + J8*J6*J2^4 + J10*J4*J2^4 + J6*J4^2*J2^4 + J8*J4*J2^5 + J10*J2^6 +
        2*J8*J2^7 + J4*J2^9 eq 0 and
	J10^2 + 2*J8^2*J4 + 2*J8*J4^3 + 2*J4^5 + 2*J10*J4^2*J2 + 2*J12*J4*J2^2 + J8*J4^2*J2^2 + 2*J4^4*J2^2 +
        2*J8*J6*J2^3 + J10*J4*J2^3 + J6*J4^2*J2^3 + J12*J2^4 + J8*J4*J2^4 + 2*J4^3*J2^4 + 2*J10*J2^5 +
        J6*J4*J2^5 + J8*J2^6 + J6*J2^7 eq 0 and
	J10*J8 + 2*J12*J6 + 2*J6*J4^3 + 2*J8^2*J2 + 2*J12*J4*J2 + J8*J4^2*J2 + 2*J8*J6*J2^2 + J6*J4^2*J2^2 +
        2*J12*J2^3 + J4^3*J2^3 + 2*J10*J2^4 + 2*J6*J4*J2^4 + J8*J2^5 + J4*J2^7 + 2*J2^9 eq 0 and
	J10*J6 + J12*J4 + J4^4 + J8*J6*J2 + 2*J10*J4*J2 + 2*J12*J2^2 + J4^3*J2^2 + J10*J2^3 + 2*J6*J4*J2^3 +
        J8*J2^4 + 2*J4^2*J2^4 + J6*J2^5 + 2*J4*J2^6 eq 0 and
	J6^2 + J8*J4 + J10*J2 + J8*J2^2 + J4^2*J2^2 + J2^6 eq 0
	then
	 vprintf G3Twists, 1 : "Automorphism group C4, curve y^2 = x*(x^2-1)*(x^4+a*x^2+b)\n";
	 aut:= SmallGroup(4, 1);
	 if models then
	     f:= Genus3Char3ConicAndQuarticForC4(JI : models:= models);
	     error if Type(f) eq BoolElt, "[G3Twists] None C4-model found at JI =", JI;
	     twists:= [f];
	 end if;
	 if geometric or not models then return twists, aut; end if;
	 return HyperellipticPolynomialTwists(f, 8), aut;
     end if;


     /*** Three dimensional case ***/

     /* D2 : y^2 = (x^2-1)*(x^6+a*x^4+b*x^2+c)  */
     if J12*J8^2 + J9*J8*J6*J5 + J9*J6*J5*J4^2 + J9*J7*J4^3 + 2*J12*J4^4 + J9*J6*J5^2*J3 + 2*J9*J7*J5*J4*J3 +
	 2*J12*J5*J4^2*J3 + 2*J7*J6*J4^3*J3 + J8*J5*J4^3*J3 + 2*J9*J4^4*J3 + 2*J5*J4^5*J3 + 2*J9*J8*J5*J3^2 +
	 J12*J5^2*J3^2 + J8*J5^2*J4*J3^2 + 2*J8*J6*J4^2*J3^2 + 2*J9*J5*J4^2*J3^2 + 2*J5^2*J4^3*J3^2 + J6*J4^4*J3^2 +
	 2*J8*J6*J5*J3^3 + 2*J9*J5^2*J3^3 + 2*J10*J5*J4*J3^3 + J8^2*J3^4 + 2*J6*J5^2*J3^4 + 2*J7*J5*J4*J3^4 + J4^4*J3^4
	 + J8*J5*J3^5 + J5*J4^2*J3^5 + 2*J5^2*J3^6 + J12*J9*J5*J2 + J9*J7*J5^2*J2 + J9*J8*J5*J4*J2 + J12*J5^2*J4*J2 +
	 J8*J6*J4^3*J2 + 2*J10*J4^4*J2 + 2*J5^2*J4^4*J2 + 2*J6*J4^5*J2 + J9*J8*J6*J3*J2 + J8*J5^3*J3*J2 +
	 2*J10*J9*J4*J3*J2 + 2*J9*J5^2*J4*J3*J2 + 2*J7*J4^4*J3*J2 + 2*J9*J6*J5*J3^2*J2 + J5^4*J3^2*J2 +
	 2*J8^2*J4*J3^2*J2 + 2*J9*J7*J4*J3^2*J2 + 2*J9*J8*J3^3*J2 + J12*J5*J3^3*J2 + 2*J7*J6*J4*J3^3*J2 +
	 J9*J4^2*J3^3*J2 + 2*J8*J6*J3^4*J2 + 2*J9*J5*J3^4*J2 + 2*J10*J4*J3^4*J2 + 2*J6*J4^2*J3^4*J2 + 2*J6*J5*J3^5*J2 +
	 J8*J3^6*J2 + J4^2*J3^6*J2 + 2*J5*J3^7*J2 + 2*J9*J8*J7*J2^2 + J9^2*J6*J2^2 + J9*J5^3*J2^2 + J9*J6*J5*J4*J2^2 +
	 2*J5^4*J4*J2^2 + J9*J7*J4^2*J2^2 + J7*J5*J4^3*J2^2 + 2*J12*J9*J3*J2^2 + J8^2*J5*J3*J2^2 + J9*J7*J5*J3*J2^2 +
	 2*J9*J8*J4*J3*J2^2 + 2*J12*J5*J4*J3*J2^2 + 2*J7*J6*J4^2*J3*J2^2 + 2*J8*J5*J4^2*J3*J2^2 + 2*J9*J4^3*J3*J2^2 +
	 2*J9^2*J3^2*J2^2 + 2*J12*J6*J3^2*J2^2 + J8*J6*J4*J3^2*J2^2 + 2*J9*J5*J4*J3^2*J2^2 + J5^2*J4^2*J3^2*J2^2 +
	 J8*J7*J3^3*J2^2 + J10*J5*J3^3*J2^2 + J5^3*J3^3*J2^2 + J7*J4^2*J3^3*J2^2 + 2*J12*J3^4*J2^2 + J7*J5*J3^4*J2^2 +
	 J8*J4*J3^4*J2^2 + 2*J9*J3^5*J2^2 + J5*J4*J3^5*J2^2 + 2*J6*J3^6*J2^2 + 2*J3^8*J2^2 + J9*J7*J6*J2^3 +
	 2*J12*J5^2*J2^3 + J9^2*J4*J2^3 + J8*J5^2*J4*J2^3 + J8*J6*J4^2*J2^3 + J9*J5*J4^2*J2^3 + 2*J10*J4^3*J2^3 +
	 J6*J4^4*J2^3 + J10*J9*J3*J2^3 + J8*J6*J5*J3*J2^3 + J9*J6*J4*J3*J2^3 + J5^3*J4*J3*J2^3 + 2*J7*J4^3*J3*J2^3 +
	 2*J8^2*J3^2*J2^3 + 2*J9*J7*J3^2*J2^3 + J6*J5^2*J3^2*J2^3 + J12*J4*J3^2*J2^3 + J8*J5*J3^3*J2^3 +
	 J9*J4*J3^3*J2^3 + 2*J10*J3^4*J2^3 + J7*J3^5*J2^3 + 2*J4*J3^6*J2^3 + J12*J8*J2^4 + J9*J6*J5*J2^4 + 2*J5^4*J2^4
	 + J8^2*J4*J2^4 + J9*J7*J4*J2^4 + 2*J7*J5*J4^2*J2^4 + J4^5*J2^4 + 2*J9*J8*J3*J2^4 + J7*J6*J4*J3*J2^4 +
	 2*J8*J5*J4*J3*J2^4 + 2*J9*J4^2*J3*J2^4 + J7^2*J3^2*J2^4 + J9*J5*J3^2*J2^4 + 2*J10*J4*J3^2*J2^4 +
	 J5^2*J4*J3^2*J2^4 + 2*J6*J5*J3^3*J2^4 + J7*J4*J3^3*J2^4 + 2*J8*J3^4*J2^4 + J4^2*J3^4*J2^4 + 2*J5*J3^5*J2^4 +
	 J9^2*J2^5 + J12*J6*J2^5 + 2*J8*J6*J4*J2^5 + J9*J5*J4*J2^5 + J10*J4^2*J2^5 + 2*J5^2*J4^2*J2^5 + J8*J7*J3*J2^5 +
	 2*J9*J6*J3*J2^5 + 2*J10*J5*J3*J2^5 + 2*J6*J5*J4*J3*J2^5 + 2*J7*J5*J3^2*J2^5 + J8*J4*J3^2*J2^5 + 2*J6*J3^4*J2^5
	 + J3^6*J2^5 + 2*J8^2*J2^6 + J12*J4*J2^6 + 2*J7*J5*J4*J2^6 + 2*J8*J4^2*J2^6 + J4^4*J2^6 + J7*J6*J3*J2^6 +
	 J8*J5*J3*J2^6 + J5*J4^2*J3*J2^6 + J10*J3^2*J2^6 + J7^2*J2^7 + 2*J8*J6*J2^7 + J9*J5*J2^7 + J10*J4*J2^7 +
	 2*J5^2*J4*J2^7 + J7*J4*J3*J2^7 + 2*J4^2*J3^2*J2^7 + 2*J8*J4*J2^8 + 2*J9*J3*J2^8 + 2*J5*J4*J3*J2^8 +
	 J6*J3^2*J2^8 + J4*J3^2*J2^9 + 2*J8*J2^10 + 2*J4^2*J2^10 + 2*J6*J2^11 + 2*J4*J2^12 + J2^14 eq 0 and
	 J8*J5^4 + J10*J9*J5*J4 + 2*J9*J5^3*J4 + 2*J9*J6*J5*J4^2 + J5^4*J4^2 + 2*J9*J7*J4^3 + 2*J12*J4^4 + 2*J8*J4^5 +
	 2*J9*J6*J5^2*J3 + J9*J7*J5*J4*J3 + 2*J12*J5*J4^2*J3 + 2*J8*J5*J4^3*J3 + 2*J9*J4^4*J3 + 2*J8*J5^2*J4*J3^2 +
	 2*J8*J6*J4^2*J3^2 + 2*J9*J5*J4^2*J3^2 + J10*J4^3*J3^2 + J5^2*J4^3*J3^2 + J6*J4^4*J3^2 + J9*J5^2*J3^3 +
	 2*J5^3*J4*J3^3 + 2*J6*J5*J4^2*J3^3 + J7*J4^3*J3^3 + J8*J4^2*J3^4 + J4^4*J3^4 + 2*J9*J7*J5^2*J2 +
	 J12*J5^2*J4*J2 + J9^2*J4^2*J2 + 2*J9*J5*J4^3*J2 + J10*J4^4*J2 + 2*J5^2*J4^4*J2 + J8*J5^3*J3*J2 +
	 2*J10*J9*J4*J3*J2 + 2*J9*J5^2*J4*J3*J2 + J9*J6*J4^2*J3*J2 + J7*J4^4*J3*J2 + 2*J9*J6*J5*J3^2*J2 + J5^4*J3^2*J2
	 + 2*J8^2*J4*J3^2*J2 + J9*J7*J4*J3^2*J2 + 2*J12*J4^2*J3^2*J2 + 2*J8*J4^3*J3^2*J2 + J4^5*J3^2*J2 +
	 J7*J6*J4*J3^3*J2 + J8*J5*J4*J3^3*J2 + J9*J4^2*J3^3*J2 + J5*J4^3*J3^3*J2 + J9*J5*J3^4*J2 + 2*J5^2*J4*J3^4*J2 +
	 2*J7*J4*J3^5*J2 + 2*J4^2*J3^6*J2 + J9*J5^3*J2^2 + 2*J9*J6*J5*J4*J2^2 + 2*J5^4*J4*J2^2 + 2*J9*J7*J4^2*J2^2 +
	 J12*J4^3*J2^2 + 2*J8*J4^4*J2^2 + 2*J8^2*J5*J3*J2^2 + 2*J9*J8*J4*J3*J2^2 + J7*J6*J4^2*J3*J2^2 + J9*J4^3*J3*J2^2
	 + 2*J5*J4^4*J3*J2^2 + 2*J12*J6*J3^2*J2^2 + J8*J5^2*J3^2*J2^2 + J8*J6*J4*J3^2*J2^2 + 2*J10*J4^2*J3^2*J2^2 +
	 2*J5^3*J3^3*J2^2 + 2*J6*J5*J4*J3^3*J2^2 + J7*J4^2*J3^3*J2^2 + J12*J3^4*J2^2 + 2*J8*J4*J3^4*J2^2 +
	 J4^3*J3^4*J2^2 + 2*J6*J3^6*J2^2 + J3^8*J2^2 + J9*J7*J6*J2^3 + 2*J12*J5^2*J2^3 + J8*J6*J4^2*J2^3 +
	 2*J10*J4^3*J2^3 + 2*J5^2*J4^3*J2^3 + J6*J4^4*J2^3 + J10*J5*J4*J3*J2^3 + J5^3*J4*J3*J2^3 + 2*J6*J5*J4^2*J3*J2^3
	 + 2*J8^2*J3^2*J2^3 + J9*J7*J3^2*J2^3 + 2*J6*J5^2*J3^2*J2^3 + 2*J12*J4*J3^2*J2^3 + J4^4*J3^2*J2^3 +
	 J7*J6*J3^3*J2^3 + J8*J5*J3^3*J2^3 + J5*J4^2*J3^3*J2^3 + J10*J3^4*J2^3 + 2*J5^2*J3^4*J2^3 + 2*J6*J4*J3^4*J2^3 +
	 2*J4*J3^6*J2^3 + 2*J9*J6*J5*J2^4 + 2*J5^4*J2^4 + J8^2*J4*J2^4 + 2*J9*J7*J4*J2^4 + J12*J4^2*J2^4 +
	 J7*J5*J4^2*J2^4 + 2*J8*J4^3*J2^4 + J4^5*J2^4 + 2*J9*J8*J3*J2^4 + 2*J12*J5*J3*J2^4 + J7*J6*J4*J3*J2^4 +
	 2*J8*J5*J4*J3*J2^4 + J9*J4^2*J3*J2^4 + 2*J5*J4^3*J3*J2^4 + 2*J7^2*J3^2*J2^4 + 2*J8*J6*J3^2*J2^4 +
	 2*J9*J5*J3^2*J2^4 + J10*J4*J3^2*J2^4 + J5^2*J4*J3^2*J2^4 + J6*J4^2*J3^2*J2^4 + 2*J6*J5*J3^3*J2^4 +
	 2*J7*J4*J3^3*J2^4 + 2*J8*J3^4*J2^4 + 2*J4^2*J3^4*J2^4 + 2*J5*J3^5*J2^4 + 2*J12*J6*J2^5 + 2*J8*J6*J4*J2^5 +
	 J9*J5*J4*J2^5 + 2*J6*J4^3*J2^5 + 2*J9*J6*J3*J2^5 + 2*J10*J5*J3*J2^5 + J6*J5*J4*J3*J2^5 + J7*J4^2*J3*J2^5 +
	 J12*J3^2*J2^5 + J7*J5*J3^2*J2^5 + J4^3*J3^2*J2^5 + J9*J3^3*J2^5 + 2*J6*J3^4*J2^5 + 2*J3^6*J2^5 + 2*J8^2*J2^6 +
	 2*J9*J7*J2^6 + 2*J6*J5^2*J2^6 + 2*J12*J4*J2^6 + J7*J5*J4*J2^6 + J8*J4^2*J2^6 + 2*J4^4*J2^6 + J9*J4*J3*J2^6 +
	 J10*J3^2*J2^6 + 2*J5^2*J3^2*J2^6 + 2*J7^2*J2^7 + J8*J6*J2^7 + 2*J9*J5*J2^7 + 2*J10*J4*J2^7 + J6*J4^2*J2^7 +
	 J4^2*J3^2*J2^7 + J5*J3^3*J2^7 + J12*J2^8 + J4^3*J2^8 + 2*J9*J3*J2^8 + 2*J5*J4*J3*J2^8 + J6*J3^2*J2^8 +
	 2*J3^4*J2^8 + 2*J6*J4*J2^9 + J7*J3*J2^9 + 2*J4*J3^2*J2^9 + 2*J8*J2^10 + J4^2*J2^10 + J5*J3*J2^10 + J6*J2^11 +
	 2*J3^2*J2^11 eq 0 and
	 J12*J5^3 + J9*J8*J6*J4 + J9*J5^2*J4^2 + 2*J10*J5*J4^3 + 2*J5^3*J4^3 + 2*J6*J5*J4^4 + 2*J9*J5^3*J3 +
	 J9*J6*J5*J4*J3 + J5^4*J4*J3 + J9*J7*J4^2*J3 + J8*J4^4*J3 + J8^2*J5*J3^2 + 2*J9*J8*J4*J3^2 + J12*J5*J4*J3^2 +
	 2*J7*J6*J4^2*J3^2 + J9*J4^3*J3^2 + J5*J4^4*J3^2 + 2*J8*J5^2*J3^3 + J8*J6*J4*J3^3 + 2*J9*J5*J4*J3^3 +
	 2*J5^3*J3^4 + J6*J5*J4*J3^4 + J7*J4^2*J3^4 + 2*J8*J4*J3^5 + 2*J9*J6*J5^2*J2 + J12*J9*J4*J2 + 2*J9*J8*J4^2*J2 +
	 J12*J5*J4^2*J2 + 2*J7*J6*J4^3*J2 + 2*J8*J5*J4^3*J2 + J9*J4^4*J2 + J5*J4^5*J2 + 2*J9*J7*J6*J3*J2 +
	 J9*J8*J5*J3*J2 + 2*J12*J5^2*J3*J2 + J8*J5^2*J4*J3*J2 + 2*J9*J5*J4^2*J3*J2 + J5^2*J4^3*J3*J2 + 2*J6*J4^4*J3*J2
	 + 2*J9*J6*J4*J3^2*J2 + 2*J10*J5*J4*J3^2*J2 + 2*J5^3*J4*J3^2*J2 + 2*J6*J5*J4^2*J3^2*J2 + J7*J4^3*J3^2*J2 +
	 J9*J7*J3^3*J2 + J12*J4*J3^3*J2 + 2*J8*J4^2*J3^3*J2 + 2*J7*J6*J3^4*J2 + 2*J9*J4*J3^4*J2 + 2*J5*J4^2*J3^4*J2 +
	 J7*J3^6*J2 + J4*J3^7*J2 + J10*J9*J4*J2^2 + J9*J6*J4^2*J2^2 + 2*J10*J5*J4^2*J2^2 + J5^3*J4^2*J2^2 +
	 2*J6*J5*J4^3*J2^2 + 2*J7*J4^4*J2^2 + 2*J9*J6*J5*J3*J2^2 + J5^4*J3*J2^2 + J8^2*J4*J3*J2^2 + J9*J7*J4*J3*J2^2 +
	 J12*J4^2*J3*J2^2 + 2*J7*J5*J4^2*J3*J2^2 + 2*J8*J4^3*J3*J2^2 + J9*J8*J3^2*J2^2 + J7*J6*J4*J3^2*J2^2 +
	 2*J9*J4^2*J3^2*J2^2 + 2*J5*J4^3*J3^2*J2^2 + 2*J8*J6*J3^3*J2^2 + J10*J4*J3^3*J2^2 + J5^2*J4*J3^3*J2^2 +
	 J6*J5*J3^4*J2^2 + 2*J8*J3^5*J2^2 + J5*J3^6*J2^2 + 2*J9*J7*J5*J2^3 + 2*J9*J8*J4*J2^3 + 2*J12*J5*J4*J2^3 +
	 2*J9*J4^3*J2^3 + J5*J4^4*J2^3 + J12*J6*J3*J2^3 + J8*J5^2*J3*J2^3 + 2*J8*J6*J4*J3*J2^3 + 2*J9*J5*J4*J3*J2^3 +
	 J10*J4^2*J3*J2^3 + 2*J5^2*J4^2*J3*J2^3 + 2*J6*J4^3*J3*J2^3 + J9*J6*J3^2*J2^3 + J10*J5*J3^2*J2^3 +
	 2*J5^3*J3^2*J2^3 + 2*J6*J5*J4*J3^2*J2^3 + J7*J4^2*J3^2*J2^3 + 2*J7*J5*J3^3*J2^3 + J8*J4*J3^3*J2^3 +
	 2*J4^3*J3^3*J2^3 + 2*J5*J4*J3^4*J2^3 + 2*J6*J3^5*J2^3 + 2*J9*J5^2*J2^4 + 2*J5^3*J4*J2^4 + J8^2*J3*J2^4 +
	 J9*J7*J3*J2^4 + 2*J12*J4*J3*J2^4 + J7*J5*J4*J3*J2^4 + J8*J4^2*J3*J2^4 + 2*J4^4*J3*J2^4 + J7*J6*J3^2*J2^4 +
	 J9*J4*J3^2*J2^4 + 2*J10*J3^3*J2^4 + J5^2*J3^3*J2^4 + 2*J4*J3^5*J2^4 + 2*J7*J5^2*J2^5 + J5*J4^3*J2^5 +
	 J7^2*J3*J2^5 + 2*J8*J6*J3*J2^5 + 2*J6*J4^2*J3*J2^5 + 2*J6*J5*J3^2*J2^5 + J8*J3^3*J2^5 + J4^2*J3^3*J2^5 +
	 J5*J3^4*J2^5 + 2*J5^3*J2^6 + 2*J7*J4^2*J2^6 + 2*J12*J3*J2^6 + 2*J8*J4*J3*J2^6 + J4^3*J3*J2^6 + J9*J3^2*J2^6 +
	 J5*J4*J3^2*J2^6 + 2*J6*J3^3*J2^6 + J3^5*J2^6 + J9*J4*J2^7 + J6*J4*J3*J2^7 + 2*J7*J3^2*J2^7 + J4*J3^3*J2^7 +
	 J8*J3*J2^8 + J5*J3^2*J2^8 + 2*J5*J4*J2^9 + 2*J6*J3*J2^9 + 2*J3^3*J2^9 + J4*J3*J2^10 eq 0 and
	 J8*J5^3*J4 + J10*J9*J4^2 + 2*J9*J5^2*J4^2 + 2*J9*J6*J4^3 + 2*J10*J5*J4^3 + 2*J5^3*J4^3 + J6*J5*J4^4 +
	 2*J9*J6*J5*J4*J3 + J9*J7*J4^2*J3 + 2*J12*J4^3*J3 + 2*J7*J5*J4^3*J3 + J4^6*J3 + J7*J6*J4^2*J3^2 +
	 2*J8*J5*J4^2*J3^2 + 2*J9*J4^3*J3^2 + J5*J4^4*J3^2 + J9*J5*J4*J3^3 + J5^2*J4^2*J3^3 + 2*J7*J4^2*J3^4 +
	 2*J4^3*J3^5 + J9*J7*J5*J4*J2 + J12*J5*J4^2*J2 + 2*J8*J5*J4^3*J2 + 2*J9*J4^4*J2 + 2*J5*J4^5*J2 + J12*J5^2*J3*J2
	 + J9*J5*J4^2*J3*J2 + 2*J6*J4^4*J3*J2 + 2*J8*J6*J5*J3^2*J2 + 2*J9*J5^2*J3^2*J2 + J9*J6*J4*J3^2*J2 +
	 2*J10*J5*J4*J3^2*J2 + J5^3*J4*J3^2*J2 + 2*J7*J4^3*J3^2*J2 + 2*J6*J5^2*J3^3*J2 + 2*J7*J5*J4*J3^3*J2 +
	 J4^4*J3^3*J2 + J8*J5*J3^4*J2 + 2*J9*J4*J3^4*J2 + 2*J5^2*J3^5*J2 + 2*J8*J5^3*J2^2 + 2*J10*J9*J4*J2^2 +
	 J10*J5*J4^2*J2^2 + J5^3*J4^2*J2^2 + 2*J6*J5*J4^3*J2^2 + 2*J9*J6*J5*J3*J2^2 + 2*J5^4*J3*J2^2 +
	 2*J7*J5*J4^2*J3*J2^2 + J7*J5^2*J3^2*J2^2 + J8*J5*J4*J3^2*J2^2 + J9*J4^2*J3^2*J2^2 + J5*J4^3*J3^2*J2^2 +
	 J10*J4*J3^3*J2^2 + J5^2*J4*J3^3*J2^2 + J7*J4*J3^4*J2^2 + 2*J4^2*J3^5*J2^2 + 2*J9*J7*J5*J2^3 + 2*J12*J5*J4*J2^3
	 + J8*J5*J4^2*J2^3 + J9*J4^3*J2^3 + 2*J5*J4^4*J2^3 + J12*J6*J3*J2^3 + 2*J8*J5^2*J3*J2^3 + J9*J5*J4*J3*J2^3 +
	 2*J5^2*J4^2*J3*J2^3 + 2*J6*J4^3*J3*J2^3 + J10*J5*J3^2*J2^3 + J6*J5*J4*J3^2*J2^3 + 2*J12*J3^3*J2^3 +
	 2*J8*J4*J3^3*J2^3 + J6*J3^5*J2^3 + 2*J3^7*J2^3 + J9*J5^2*J2^4 + J9*J6*J4*J2^4 + 2*J5^3*J4*J2^4 + J8^2*J3*J2^4
	 + J9*J7*J3*J2^4 + 2*J6*J5^2*J3*J2^4 + J12*J4*J3*J2^4 + J7*J5*J4*J3*J2^4 + 2*J8*J4^2*J3*J2^4 + J7*J6*J3^2*J2^4
	 + J8*J5*J3^2*J2^4 + 2*J9*J4*J3^2*J2^4 + 2*J5*J4^2*J3^2*J2^4 + 2*J10*J3^3*J2^4 + 2*J5^2*J3^3*J2^4 +
	 2*J6*J4*J3^3*J2^4 + J7*J3^4*J2^4 + J4*J3^5*J2^4 + 2*J9*J4^2*J2^5 + J5*J4^3*J2^5 + J7^2*J3*J2^5 +
	 2*J8*J6*J3*J2^5 + J9*J5*J3*J2^5 + J10*J4*J3*J2^5 + 2*J5^2*J4*J3*J2^5 + 2*J6*J5*J3^2*J2^5 + 2*J7*J4*J3^2*J2^5 +
	 J8*J3^3*J2^5 + J4^2*J3^3*J2^5 + J5*J3^4*J2^5 + J5^3*J2^6 + 2*J12*J3*J2^6 + 2*J7*J5*J3*J2^6 + J8*J4*J3*J2^6 +
	 2*J9*J3^2*J2^6 + J5*J4*J3^2*J2^6 + J6*J3^3*J2^6 + J3^5*J2^6 + J9*J4*J2^7 + 2*J5*J4^2*J2^7 + 2*J6*J4*J3*J2^7 +
	 2*J7*J3^2*J2^7 + J4*J3^3*J2^7 + J8*J3*J2^8 + J5*J3^2*J2^8 + 2*J5*J4*J2^9 + 2*J6*J3*J2^9 + J3^3*J2^9 +
	 J4*J3*J2^10 eq 0 and
	 J12*J8*J6 + J9*J7*J5^2 + 2*J9*J8*J5*J4 + 2*J8*J5^2*J4^2 + 2*J8*J6*J4^3 + 2*J9*J5*J4^3 + J10*J4^4 + J5^2*J4^4 +
	 2*J6*J4^5 + 2*J8*J5^3*J3 + J9*J5^2*J4*J3 + J9*J6*J4^2*J3 + J10*J5*J4^2*J3 + J5^3*J4^2*J3 + J7*J4^4*J3 +
	 2*J12*J8*J3^2 + J8^2*J4*J3^2 + 2*J12*J4^2*J3^2 + J7*J5*J4^2*J3^2 + 2*J7*J6*J4*J3^3 + 2*J9*J4^2*J3^3 +
	 J8*J6*J3^4 + J7*J4*J3^5 + 2*J8*J3^6 + 2*J4^2*J3^6 + J9*J8*J7*J2 + J10*J9*J5*J2 + J9*J5^3*J2 + J9*J7*J4^2*J2 +
	 J12*J4^3*J2 + 2*J7*J5*J4^3*J2 + 2*J4^6*J2 + 2*J8^2*J5*J3*J2 + J9*J7*J5*J3*J2 + 2*J9*J8*J4*J3*J2 +
	 J12*J5*J4*J3*J2 + 2*J7*J6*J4^2*J3*J2 + 2*J9*J4^3*J3*J2 + J5*J4^4*J3*J2 + J12*J6*J3^2*J2 + J8*J6*J4*J3^2*J2 +
	 2*J9*J5*J4*J3^2*J2 + J10*J4^2*J3^2*J2 + J6*J4^3*J3^2*J2 + J8*J7*J3^3*J2 + 2*J6*J5*J4*J3^3*J2 + 2*J12*J3^4*J2 +
	 J7*J5*J3^4*J2 + 2*J8*J4*J3^4*J2 + 2*J4^3*J3^4*J2 + J6*J3^6*J2 + 2*J3^8*J2 + J9*J8*J5*J2^2 + 2*J12*J5^2*J2^2 +
	 J9^2*J4*J2^2 + J8*J5^2*J4*J2^2 + 2*J8*J6*J4^2*J2^2 + J9*J5*J4^2*J2^2 + 2*J10*J4^3*J2^2 + J8*J6*J5*J3*J2^2 +
	 J9*J6*J4*J3*J2^2 + J10*J5*J4*J3*J2^2 + J7*J4^3*J3*J2^2 + 2*J8^2*J3^2*J2^2 + J6*J5^2*J3^2*J2^2 +
	 J7*J5*J4*J3^2*J2^2 + 2*J7*J6*J3^3*J2^2 + J9*J4*J3^3*J2^2 + 2*J5^2*J3^4*J2^2 + 2*J6*J4*J3^4*J2^2 + J7*J3^5*J2^2
	 + 2*J4*J3^6*J2^2 + 2*J9*J6*J5*J2^3 + J5^4*J2^3 + J8^2*J4*J2^3 + 2*J12*J4^2*J2^3 + 2*J7*J5*J4^2*J2^3 +
	 2*J4^5*J2^3 + 2*J9*J8*J3*J2^3 + 2*J12*J5*J3*J2^3 + 2*J7*J5^2*J3*J2^3 + 2*J7*J6*J4*J3*J2^3 + 2*J9*J4^2*J3*J2^3
	 + 2*J7^2*J3^2*J2^3 + J8*J6*J3^2*J2^3 + 2*J9*J5*J3^2*J2^3 + 2*J10*J4*J3^2*J2^3 + 2*J5^2*J4*J3^2*J2^3 +
	 J6*J4^2*J3^2*J2^3 + 2*J6*J5*J3^3*J2^3 + 2*J8*J3^4*J2^3 + J4^2*J3^4*J2^3 + J5*J3^5*J2^3 + 2*J9^2*J2^4 +
	 2*J12*J6*J2^4 + J8*J5^2*J2^4 + 2*J8*J6*J4*J2^4 + J9*J5*J4*J2^4 + J6*J4^3*J2^4 + 2*J8*J7*J3*J2^4 +
	 J9*J6*J3*J2^4 + J6*J5*J4*J3*J2^4 + 2*J12*J3^2*J2^4 + 2*J7*J5*J3^2*J2^4 + J8*J4*J3^2*J2^4 + J4^3*J3^2*J2^4 +
	 2*J9*J3^3*J2^4 + J5*J4*J3^3*J2^4 + J3^6*J2^4 + J9*J7*J2^5 + J6*J5^2*J2^5 + 2*J7*J5*J4*J2^5 + 2*J8*J4^2*J2^5 +
	 J4^4*J2^5 + 2*J7*J6*J3*J2^5 + J9*J4*J3*J2^5 + 2*J5*J4^2*J3*J2^5 + J10*J3^2*J2^5 + J5^2*J3^2*J2^5 +
	 J6*J4*J3^2*J2^5 + 2*J4*J3^4*J2^5 + J8*J6*J2^6 + 2*J9*J5*J2^6 + 2*J10*J4*J2^6 + J5^2*J4*J2^6 + 2*J6*J4^2*J2^6 +
	 J6*J5*J3*J2^6 + J7*J4*J3*J2^6 + J8*J3^2*J2^6 + J4^2*J3^2*J2^6 + J7*J5*J2^7 + J8*J4*J2^7 + J4^3*J2^7 +
	 J5*J4*J3*J2^7 + 2*J3^4*J2^7 + J5^2*J2^8 + 2*J6*J4*J2^8 + 2*J7*J3*J2^8 + 2*J4*J3^2*J2^8 + 2*J5*J3*J2^9 +
	 2*J6*J2^10 + 2*J3^2*J2^10 + 2*J4*J2^11 eq 0 and
	 J8^2*J5^2 + J9*J7*J5^2 + 2*J5^2*J4^4 + J8*J5^3*J3 + J9*J5^2*J4*J3 + J9*J6*J4^2*J3 + J5^3*J4^2*J3 +
	 2*J6*J5*J4^3*J3 + 2*J8^2*J4*J3^2 + 2*J12*J4^2*J3^2 + 2*J7*J5*J4^2*J3^2 + 2*J8*J4^3*J3^2 + 2*J4^5*J3^2 +
	 2*J7*J6*J4*J3^3 + J8*J5*J4*J3^3 + 2*J9*J4^2*J3^3 + J5*J4^3*J3^3 + J7*J4*J3^5 + 2*J4^2*J3^6 + 2*J10*J9*J5*J2 +
	 J9*J5^3*J2 + J5^4*J4*J2 + J9*J7*J4^2*J2 + 2*J7*J5*J4^3*J2 + J9*J7*J5*J3*J2 + 2*J7*J6*J4^2*J3*J2 +
	 2*J8*J5*J4^2*J3*J2 + 2*J5*J4^4*J3*J2 + 2*J12*J6*J3^2*J2 + 2*J8*J5^2*J3^2*J2 + J8*J6*J4*J3^2*J2 +
	 2*J9*J5*J4*J3^2*J2 + J6*J4^3*J3^2*J2 + 2*J10*J5*J3^3*J2 + J5^3*J3^3*J2 + J6*J5*J4*J3^3*J2 + J12*J3^4*J2 +
	 2*J7*J5*J3^4*J2 + J4^3*J3^4*J2 + J5*J4*J3^5*J2 + 2*J6*J3^6*J2 + J3^8*J2 + J9^2*J4*J2^2 + 2*J8*J5^2*J4*J2^2 +
	 J8*J6*J4^2*J2^2 + J10*J4^3*J2^2 + 2*J6*J4^4*J2^2 + J9*J5^2*J3*J2^2 + J9*J6*J4*J3*J2^2 + 2*J10*J5*J4*J3*J2^2 +
	 J6*J5*J4^2*J3*J2^2 + 2*J7*J4^3*J3*J2^2 + 2*J8^2*J3^2*J2^2 + 2*J9*J7*J3^2*J2^2 + J6*J5^2*J3^2*J2^2 +
	 2*J12*J4*J3^2*J2^2 + J7*J5*J4*J3^2*J2^2 + J8*J4^2*J3^2*J2^2 + 2*J4^4*J3^2*J2^2 + 2*J5*J4^2*J3^3*J2^2 +
	 J10*J3^4*J2^2 + J7*J3^5*J2^2 + J9*J6*J5*J2^3 + 2*J5^4*J2^3 + J8^2*J4*J2^3 + J12*J4^2*J2^3 + J7*J5*J4^2*J2^3 +
	 J4^5*J2^3 + 2*J12*J5*J3*J2^3 + 2*J7*J5^2*J3*J2^3 + J7*J6*J4*J3*J2^3 + J8*J5*J4*J3*J2^3 + 2*J7^2*J3^2*J2^3 +
	 J8*J6*J3^2*J2^3 + J5^2*J4*J3^2*J2^3 + 2*J6*J5*J3^3*J2^3 + J7*J4*J3^3*J2^3 + J8*J3^4*J2^3 + 2*J4^2*J3^4*J2^3 +
	 J5*J3^5*J2^3 + 2*J12*J6*J2^4 + 2*J8*J5^2*J2^4 + 2*J8*J6*J4*J2^4 + J10*J4^2*J2^4 + 2*J10*J5*J3*J2^4 +
	 J5^3*J3*J2^4 + 2*J6*J5*J4*J3*J2^4 + J7*J4^2*J3*J2^4 + 2*J12*J3^2*J2^4 + 2*J7*J5*J3^2*J2^4 + 2*J8*J4*J3^2*J2^4
	 + 2*J4^3*J3^2*J2^4 + J9*J3^3*J2^4 + 2*J8^2*J2^5 + 2*J9*J7*J2^5 + 2*J6*J5^2*J2^5 + 2*J12*J4*J2^5 +
	 2*J8*J4^2*J2^5 + J7*J6*J3*J2^5 + J8*J5*J3*J2^5 + 2*J5*J4^2*J3*J2^5 + J10*J3^2*J2^5 + J6*J4*J3^2*J2^5 +
	 J7*J3^3*J2^5 + J4*J3^4*J2^5 + 2*J7^2*J2^6 + J8*J6*J2^6 + 2*J10*J4*J2^6 + 2*J6*J5*J3*J2^6 + J7*J4*J3*J2^6 +
	 2*J8*J3^2*J2^6 + 2*J5*J3^3*J2^6 + J12*J2^7 + J4^3*J2^7 + J9*J3*J2^7 + J5*J4*J3*J2^7 + J6*J3^2*J2^7 +
	 2*J3^4*J2^7 + J5^2*J2^8 + 2*J6*J4*J2^8 + J7*J3*J2^8 + 2*J8*J2^9 + 2*J4^2*J2^9 + 2*J5*J3*J2^9 + J6*J2^10 +
	 J3^2*J2^10 eq 0 and
	 J9*J7*J6*J4 + 2*J12*J5^2*J4 + J8*J5^2*J4^2 + J8*J6*J4^3 + J9*J5*J4^3 + 2*J10*J4^4 + 2*J6*J4^5 +
	 2*J9*J6*J4^2*J3 + J10*J5*J4^2*J3 + J5^3*J4^2*J3 + J6*J5*J4^3*J3 + 2*J8^2*J4*J3^2 + 2*J9*J7*J4*J3^2 +
	 2*J12*J4^2*J3^2 + 2*J8*J4^3*J3^2 + 2*J7*J6*J4*J3^3 + J8*J5*J4*J3^3 + J9*J4^2*J3^3 + 2*J5^2*J4*J3^4 +
	 J7*J4*J3^5 + 2*J4^2*J3^6 + 2*J9*J6*J5*J4*J2 + 2*J5^4*J4*J2 + 2*J9*J7*J4^2*J2 + J12*J4^3*J2 + J8^2*J5*J3*J2 +
	 J9*J7*J5*J3*J2 + J9*J8*J4*J3*J2 + J12*J5*J4*J3*J2 + 2*J8*J5*J4^2*J3*J2 + J9*J4^3*J3*J2 + J5*J4^4*J3*J2 +
	 2*J12*J6*J3^2*J2 + 2*J8*J5^2*J3^2*J2 + 2*J9*J5*J4*J3^2*J2 + J5^2*J4^2*J3^2*J2 + J6*J4^3*J3^2*J2 +
	 2*J10*J5*J3^3*J2 + 2*J7*J4^2*J3^3*J2 + J12*J3^4*J2 + 2*J7*J5*J3^4*J2 + J8*J4*J3^4*J2 + 2*J4^3*J3^4*J2 +
	 2*J6*J3^6*J2 + J3^8*J2 + 2*J9*J7*J6*J2^2 + J12*J5^2*J2^2 + 2*J8*J5^2*J4*J2^2 + 2*J8*J6*J4^2*J2^2 +
	 J10*J4^3*J2^2 + 2*J5^2*J4^3*J2^2 + 2*J8*J6*J5*J3*J2^2 + J9*J6*J4*J3*J2^2 + J10*J5*J4*J3*J2^2 +
	 2*J6*J5*J4^2*J3*J2^2 + 2*J7*J4^3*J3*J2^2 + 2*J8^2*J3^2*J2^2 + J6*J5^2*J3^2*J2^2 + 2*J12*J4*J3^2*J2^2 +
	 J7*J5*J4*J3^2*J2^2 + J8*J4^2*J3^2*J2^2 + 2*J7*J6*J3^3*J2^2 + J8*J5*J3^3*J2^2 + J10*J3^4*J2^2 +
	 2*J5^2*J3^4*J2^2 + 2*J7*J3^5*J2^2 + J9*J6*J5*J2^3 + J8^2*J4*J2^3 + 2*J12*J4^2*J2^3 + 2*J7*J5*J4^2*J2^3 +
	 J4^5*J2^3 + J9*J8*J3*J2^3 + J12*J5*J3*J2^3 + J7*J6*J4*J3*J2^3 + J8*J5*J4*J3*J2^3 + J9*J4^2*J3*J2^3 +
	 J5*J4^3*J3*J2^3 + 2*J7^2*J3^2*J2^3 + 2*J9*J5*J3^2*J2^3 + J10*J4*J3^2*J2^3 + 2*J5^2*J4*J3^2*J2^3 +
	 J6*J5*J3^3*J2^3 + J7*J4*J3^3*J2^3 + J12*J6*J2^4 + 2*J8*J5^2*J2^4 + 2*J8*J6*J4*J2^4 + J9*J5*J4*J2^4 +
	 2*J10*J4^2*J2^4 + 2*J5^2*J4^2*J2^4 + 2*J6*J4^3*J2^4 + J9*J6*J3*J2^4 + 2*J5^3*J3*J2^4 + J6*J5*J4*J3*J2^4 +
	 2*J7*J4^2*J3*J2^4 + J12*J3^2*J2^4 + 2*J7*J5*J3^2*J2^4 + 2*J8*J4*J3^2*J2^4 + J4^3*J3^2*J2^4 + J9*J3^3*J2^4 +
	 J5*J4*J3^3*J2^4 + 2*J3^6*J2^4 + J8^2*J2^5 + J9*J7*J2^5 + 2*J6*J5^2*J2^5 + J7*J6*J3*J2^5 + 2*J8*J5*J3*J2^5 +
	 2*J9*J4*J3*J2^5 + 2*J5*J4^2*J3*J2^5 + 2*J10*J3^2*J2^5 + J5^2*J3^2*J2^5 + 2*J6*J4*J3^2*J2^5 + J7*J3^3*J2^5 +
	 J4*J3^4*J2^5 + J7^2*J2^6 + 2*J8*J6*J2^6 + J9*J5*J2^6 + 2*J10*J4*J2^6 + J5^2*J4*J2^6 + J6*J4^2*J2^6 +
	 J7*J4*J3*J2^6 + 2*J5*J3^3*J2^6 + 2*J12*J2^7 + 2*J7*J5*J2^7 + 2*J8*J4*J2^7 + J9*J3*J2^7 + J3^4*J2^7 +
	 2*J6*J4*J2^8 + 2*J7*J3*J2^8 + 2*J4*J3^2*J2^8 + J8*J2^9 + J4^2*J2^9 + J5*J3*J2^9 + 2*J6*J2^10 + 2*J3^2*J2^10 eq 0 and
	 J12*J8*J5 + J9*J6*J5^2 + 2*J12*J5*J4^2 + 2*J8*J5*J4^3 + J5*J4^5 + 2*J12*J5^2*J3 + J8*J5^2*J4*J3 +
	 2*J8*J6*J4^2*J3 + J10*J4^3*J3 + J6*J4^4*J3 + J8*J6*J5*J3^2 + 2*J9*J5^2*J3^2 + 2*J6*J5*J4^2*J3^2 + J7*J4^3*J3^2
	 + J6*J5^2*J3^3 + J8*J4^2*J3^3 + 2*J4^4*J3^3 + J5^2*J3^5 + 2*J9*J8*J6*J2 + 2*J9*J5^2*J4*J2 + J9*J6*J4^2*J2 +
	 J9*J6*J5*J3*J2 + 2*J5^4*J3*J2 + J8^2*J4*J3*J2 + J12*J4^2*J3*J2 + J4^5*J3*J2 + J9*J8*J3^2*J2 + J12*J5*J3^2*J2 +
	 2*J7*J5^2*J3^2*J2 + J7*J6*J4*J3^2*J2 + 2*J8*J5*J4*J3^2*J2 + 2*J9*J4^2*J3^2*J2 + J5*J4^3*J3^2*J2 +
	 2*J8*J6*J3^3*J2 + 2*J9*J5*J3^3*J2 + 2*J6*J5*J3^4*J2 + 2*J7*J4*J3^4*J2 + J8*J3^5*J2 + J4^2*J3^5*J2 +
	 2*J5*J3^6*J2 + J12*J9*J2^2 + J9*J8*J4*J2^2 + J12*J5*J4*J2^2 + 2*J7*J6*J4^2*J2^2 + J12*J6*J3*J2^2 +
	 J8*J5^2*J3*J2^2 + 2*J8*J6*J4*J3*J2^2 + J9*J5*J4*J3*J2^2 + 2*J5^2*J4^2*J3*J2^2 + J6*J4^3*J3*J2^2 +
	 J5^3*J3^2*J2^2 + J6*J5*J4*J3^2*J2^2 + J7*J4^2*J3^2*J2^2 + 2*J7*J5*J3^3*J2^2 + J8*J4*J3^3*J2^2 + J4^3*J3^3*J2^2
	 + J9*J3^4*J2^2 + 2*J5*J4*J3^4*J2^2 + J6*J3^5*J2^2 + 2*J9*J6*J4*J2^3 + 2*J10*J5*J4*J2^3 + 2*J5^3*J4*J2^3 +
	 2*J6*J5*J4^2*J2^3 + J7*J4^3*J2^3 + J8^2*J3*J2^3 + J12*J4*J3*J2^3 + 2*J7*J5*J4*J3*J2^3 + J8*J4^2*J3*J2^3 +
	 2*J9*J4*J3^2*J2^3 + 2*J10*J3^3*J2^3 + J5^2*J3^3*J2^3 + 2*J6*J4*J3^3*J2^3 + J7*J3^4*J2^3 + 2*J4*J3^5*J2^3 +
	 2*J12*J5*J2^4 + J7*J5^2*J2^4 + 2*J5*J4^3*J2^4 + J7^2*J3*J2^4 + J9*J5*J3*J2^4 + 2*J10*J4*J3*J2^4 +
	 J5^2*J4*J3*J2^4 + J7*J4*J3^2*J2^4 + J8*J3^3*J2^4 + J5*J3^4*J2^4 + J9*J6*J2^5 + 2*J5^3*J2^5 + J6*J5*J4*J2^5 +
	 J12*J3*J2^5 + 2*J7*J5*J3*J2^5 + J8*J4*J3*J2^5 + 2*J4^3*J3*J2^5 + 2*J5*J4*J3^2*J2^5 + J3^5*J2^5 + J8*J5*J2^6 +
	 J8*J3*J2^7 + 2*J4^2*J3*J2^7 + J5*J3^2*J2^7 + J9*J2^8 + 2*J5*J4*J2^8 + J6*J3*J2^8 + J4*J3*J2^9 + 2*J5*J2^10 +
	 2*J3*J2^11 eq 0 and
	 J5^5 + 2*J9*J8*J4^2 + J12*J5*J4^2 + 2*J8*J5*J4^3 + J9*J4^4 + 2*J5*J4^5 + J12*J5^2*J3 + 2*J8*J6*J4^2*J3 +
	 2*J9*J5*J4^2*J3 + J6*J4^4*J3 + J8*J6*J5*J3^2 + 2*J10*J5*J4*J3^2 + 2*J7*J4^3*J3^2 + J6*J5^2*J3^3 +
	 2*J7*J5*J4*J3^3 + 2*J4^4*J3^3 + 2*J8*J5*J3^4 + 2*J8*J5^3*J2 + J10*J9*J4*J2 + J9*J6*J4^2*J2 + 2*J10*J5*J4^2*J2
	 + 2*J5^3*J4^2*J2 + J6*J5*J4^3*J2 + 2*J7*J4^4*J2 + J9*J6*J5*J3*J2 + J5^4*J3*J2 + J8^2*J4*J3*J2 + J12*J4^2*J3*J2
	 + 2*J8*J4^3*J3*J2 + J7*J5^2*J3^2*J2 + 2*J7*J6*J4*J3^2*J2 + J8*J5*J4*J3^2*J2 + 2*J9*J5*J3^3*J2 +
	 2*J10*J4*J3^3*J2 + J5^2*J4*J3^3*J2 + 2*J6*J4^2*J3^3*J2 + 2*J4^2*J3^5*J2 + 2*J9*J7*J5*J2^2 + 2*J9*J8*J4*J2^2 +
	 2*J12*J5*J4*J2^2 + 2*J8*J5*J4^2*J2^2 + J8*J6*J4*J3*J2^2 + 2*J9*J5*J4*J3*J2^2 + 2*J10*J4^2*J3*J2^2 +
	 J6*J4^3*J3*J2^2 + J7*J4^2*J3^2*J2^2 + 2*J8*J4*J3^3*J2^2 + 2*J4^3*J3^3*J2^2 + 2*J5*J4*J3^4*J2^2 + J9*J6*J4*J2^3
	 + 2*J6*J5^2*J3*J2^3 + J12*J4*J3*J2^3 + J7*J5*J4*J3*J2^3 + 2*J8*J4^2*J3*J2^3 + 2*J4^4*J3*J2^3 +
	 2*J7*J6*J3^2*J2^3 + 2*J8*J5*J3^2*J2^3 + J9*J4*J3^2*J2^3 + J5*J4^2*J3^2*J2^3 + J7*J3^4*J2^3 + J4*J3^5*J2^3 +
	 J7*J5^2*J2^4 + J9*J4^2*J2^4 + 2*J5*J4^3*J2^4 + J6*J4^2*J3*J2^4 + 2*J6*J5*J3^2*J2^4 + 2*J7*J4*J3^2*J2^4 +
	 J8*J3^3*J2^4 + J4^2*J3^3*J2^4 + J5*J3^4*J2^4 + J7*J4^2*J2^5 + 2*J7*J5*J3*J2^5 + J8*J4*J3*J2^5 + 2*J4^3*J3*J2^5
	 + J6*J3^3*J2^5 + 2*J5*J4^2*J2^6 + 2*J6*J4*J3*J2^6 + J5*J3^2*J2^7 + 2*J5*J4*J2^8 + 2*J3^3*J2^8 + 2*J4*J3*J2^9 eq 0 and
	 J8^2*J5*J4 + J9*J7*J5*J4 + 2*J5*J4^5 + J8*J5^2*J4*J3 + J8*J6*J4^2*J3 + J9*J5*J4^2*J3 + 2*J10*J4^3*J3 +
	 J5^2*J4^3*J3 + 2*J6*J4^4*J3 + J6*J5*J4^2*J3^2 + 2*J7*J4^3*J3^2 + 2*J8*J4^2*J3^3 + J4^4*J3^3 + 2*J5*J4^2*J3^4 +
	 2*J8*J5^3*J2 + J10*J9*J4*J2 + 2*J9*J5^2*J4*J2 + J9*J6*J4^2*J2 + 2*J10*J5*J4^2*J2 + J5^3*J4^2*J2 +
	 2*J6*J5*J4^3*J2 + J9*J6*J5*J3*J2 + 2*J8^2*J4*J3*J2 + 2*J9*J7*J4*J3*J2 + 2*J7*J5*J4^2*J3*J2 + J8*J4^3*J3*J2 +
	 J7*J6*J4*J3^2*J2 + J8*J5*J4*J3^2*J2 + J9*J4^2*J3^2*J2 + J5*J4^3*J3^2*J2 + 2*J9*J5*J3^3*J2 + J5^2*J4*J3^3*J2 +
	 2*J7*J4*J3^4*J2 + J9*J7*J5*J2^2 + 2*J12*J5*J4*J2^2 + 2*J7*J6*J4^2*J2^2 + J8*J5*J4^2*J2^2 + 2*J5*J4^4*J2^2 +
	 2*J12*J6*J3*J2^2 + J8*J5^2*J3*J2^2 + J8*J6*J4*J3*J2^2 + J9*J5*J4*J3*J2^2 + 2*J10*J4^2*J3*J2^2 +
	 2*J5^2*J4^2*J3*J2^2 + 2*J6*J4^3*J3*J2^2 + 2*J10*J5*J3^2*J2^2 + 2*J5^3*J3^2*J2^2 + 2*J6*J5*J4*J3^2*J2^2 +
	 J7*J4^2*J3^2*J2^2 + J12*J3^3*J2^2 + 2*J7*J5*J3^3*J2^2 + J8*J4*J3^3*J2^2 + J5*J4*J3^4*J2^2 + 2*J6*J3^5*J2^2 +
	 J3^7*J2^2 + 2*J8*J6*J5*J2^3 + 2*J9*J5^2*J2^3 + 2*J5^3*J4*J2^3 + J6*J5*J4^2*J2^3 + J7*J4^3*J2^3 +
	 2*J8^2*J3*J2^3 + 2*J9*J7*J3*J2^3 + J6*J5^2*J3*J2^3 + 2*J12*J4*J3*J2^3 + 2*J7*J5*J4*J3*J2^3 + J4^4*J3*J2^3 +
	 J8*J5*J3^2*J2^3 + J9*J4*J3^2*J2^3 + J10*J3^3*J2^3 + 2*J5^2*J3^3*J2^3 + J7*J3^4*J2^3 + J4*J3^5*J2^3 +
	 J12*J5*J2^4 + J7*J5^2*J2^4 + J7*J6*J4*J2^4 + 2*J8*J5*J4*J2^4 + 2*J9*J4^2*J2^4 + J5*J4^3*J2^4 + 2*J7^2*J3*J2^4
	 + J8*J6*J3*J2^4 + J9*J5*J3*J2^4 + 2*J5^2*J4*J3*J2^4 + 2*J6*J4^2*J3*J2^4 + 2*J7*J4*J3^2*J2^4 + J8*J3^3*J2^4 +
	 2*J4^2*J3^3*J2^4 + 2*J5^3*J2^5 + J6*J5*J4*J2^5 + 2*J7*J4^2*J2^5 + J12*J3*J2^5 + J7*J5*J3*J2^5 + J8*J4*J3*J2^5
	 + J4^3*J3*J2^5 + J9*J3^2*J2^5 + J5*J4*J3^2*J2^5 + J6*J3^3*J2^5 + 2*J3^5*J2^5 + 2*J9*J4*J2^6 + 2*J5*J4^2*J2^6 +
	 J6*J4*J3*J2^6 + J7*J3^2*J2^6 + 2*J4*J3^3*J2^6 + J6*J5*J2^7 + 2*J8*J3*J2^7 + J6*J3*J2^8 + J5*J2^10 eq 0 and
	 J12^2 + J9*J8*J7 + 2*J10*J9*J5 + J5^4*J4 + 2*J9*J7*J4^2 + 2*J12*J4^3 + J7*J5*J4^3 + 2*J8*J4^4 + 2*J4^6 +
	 J9*J8*J4*J3 + 2*J12*J5*J4*J3 + J7*J6*J4^2*J3 + J9*J4^3*J3 + 2*J5*J4^4*J3 + 2*J12*J6*J3^2 + 2*J8*J5^2*J3^2 +
	 J10*J4^2*J3^2 + 2*J5^2*J4^2*J3^2 + J8*J7*J3^3 + J10*J5*J3^3 + J6*J5*J4*J3^3 + 2*J7*J5*J3^4 + 2*J4^3*J3^4 +
	 J5*J4*J3^5 + 2*J6*J3^6 + 2*J3^8 + 2*J9*J8*J5*J2 + J9^2*J4*J2 + J8*J5^2*J4*J2 + 2*J8*J6*J4^2*J2 + J9*J5*J4^2*J2
	 + J10*J4^3*J2 + J5^2*J4^3*J2 + J6*J4^4*J2 + 2*J8*J6*J5*J3*J2 + J10*J5*J4*J3*J2 + J5^3*J4*J3*J2 +
	 2*J6*J5*J4^2*J3*J2 + J7*J4^3*J3*J2 + 2*J8^2*J3^2*J2 + J9*J7*J3^2*J2 + J12*J4*J3^2*J2 + 2*J7*J5*J4*J3^2*J2 +
	 2*J8*J4^2*J3^2*J2 + J9*J4*J3^3*J2 + 2*J10*J3^4*J2 + 2*J5^2*J3^4*J2 + 2*J6*J4*J3^4*J2 + 2*J7*J3^5*J2 +
	 2*J4*J3^6*J2 + J9*J6*J5*J2^2 + J5^4*J2^2 + J12*J4^2*J2^2 + 2*J7*J5*J4^2*J2^2 + J4^5*J2^2 + 2*J9*J8*J3*J2^2 +
	 2*J12*J5*J3*J2^2 + 2*J7^2*J3^2*J2^2 + J9*J5*J3^2*J2^2 + J10*J4*J3^2*J2^2 + 2*J6*J5*J3^3*J2^2 + 2*J8*J3^4*J2^2
	 + 2*J4^2*J3^4*J2^2 + 2*J5*J3^5*J2^2 + 2*J9^2*J2^3 + 2*J12*J6*J2^3 + J8*J5^2*J2^3 + J9*J5*J4*J2^3 +
	 J10*J4^2*J2^3 + 2*J8*J7*J3*J2^3 + J9*J6*J3*J2^3 + 2*J5^3*J3*J2^3 + J6*J5*J4*J3*J2^3 + 2*J12*J3^2*J2^3 +
	 J7*J5*J3^2*J2^3 + 2*J8*J4*J3^2*J2^3 + 2*J4^3*J3^2*J2^3 + J9*J3^3*J2^3 + J6*J3^4*J2^3 + 2*J8^2*J2^4 +
	 2*J12*J4*J2^4 + 2*J7*J6*J3*J2^4 + J8*J5*J3*J2^4 + 2*J9*J4*J3*J2^4 + 2*J10*J3^2*J2^4 + 2*J6*J4*J3^2*J2^4 +
	 2*J4*J3^4*J2^4 + 2*J7^2*J2^5 + J8*J6*J2^5 + 2*J9*J5*J2^5 + J5^2*J4*J2^5 + 2*J7*J4*J3*J2^5 + J4^2*J3^2*J2^5 +
	 2*J5*J3^3*J2^5 + 2*J7*J5*J2^6 + 2*J8*J4*J2^6 + 2*J4^3*J2^6 + J9*J3*J2^6 + J5*J4*J3*J2^6 + 2*J5^2*J2^7 +
	 J4*J3^2*J2^7 + 2*J8*J2^8 + J6*J2^9 + J3^2*J2^9 + J4*J2^10 + J2^12 eq 0 and
	 J8^3 + 2*J9*J5^3 + J9*J6*J5*J4 + 2*J9*J7*J4^2 + 2*J8*J4^4 + 2*J8^2*J5*J3 + 2*J12*J5*J4*J3 + J7*J6*J4^2*J3 +
	 J8*J5*J4^2*J3 + 2*J9*J4^3*J3 + J8*J5^2*J3^2 + 2*J8*J6*J4*J3^2 + 2*J9*J5*J4*J3^2 + J5^2*J4^2*J3^2 +
	 2*J6*J5*J4*J3^3 + 2*J7*J4^2*J3^3 + J8*J4*J3^4 + J9*J7*J6*J2 + 2*J12*J5^2*J2 + J8*J5^2*J4*J2 + J5^3*J4*J3*J2 +
	 J6*J5*J4^2*J3*J2 + 2*J9*J7*J3^2*J2 + 2*J12*J4*J3^2*J2 + 2*J7*J5*J4*J3^2*J2 + J8*J4^2*J3^2*J2 + J4^4*J3^2*J2 +
	 J7*J6*J3^3*J2 + 2*J5*J4^2*J3^3*J2 + J5^2*J3^4*J2 + 2*J7*J3^5*J2 + 2*J4*J3^6*J2 + J12*J8*J2^2 + 2*J5^4*J2^2 +
	 J8^2*J4*J2^2 + J12*J4^2*J2^2 + 2*J7*J5*J4^2*J2^2 + 2*J9*J8*J3*J2^2 + 2*J12*J5*J3*J2^2 + J7*J5^2*J3*J2^2 +
	 J8*J5*J4*J3*J2^2 + J9*J4^2*J3*J2^2 + 2*J8*J6*J3^2*J2^2 + 2*J9*J5*J3^2*J2^2 + 2*J10*J4*J3^2*J2^2 +
	 2*J5^2*J4*J3^2*J2^2 + 2*J7*J4*J3^3*J2^2 + J8*J3^4*J2^2 + 2*J4^2*J3^4*J2^2 + J9^2*J2^3 + J12*J6*J2^3 +
	 J8*J5^2*J2^3 + J8*J6*J4*J2^3 + 2*J9*J5*J4*J2^3 + 2*J5^2*J4^2*J2^3 + 2*J8*J7*J3*J2^3 + 2*J9*J6*J3*J2^3 +
	 J5^3*J3*J2^3 + 2*J6*J5*J4*J3*J2^3 + J7*J5*J3^2*J2^3 + J4^3*J3^2*J2^3 + 2*J5*J4*J3^3*J2^3 + J8^2*J2^4 +
	 2*J12*J4*J2^4 + 2*J7*J5*J4*J2^4 + J8*J4^2*J2^4 + 2*J7*J6*J3*J2^4 + 2*J8*J5*J3*J2^4 + 2*J9*J4*J3*J2^4 +
	 2*J10*J3^2*J2^4 + 2*J5^2*J3^2*J2^4 + J6*J4*J3^2*J2^4 + 2*J7*J3^3*J2^4 + J4*J3^4*J2^4 + 2*J7^2*J2^5 +
	 2*J8*J6*J2^5 + 2*J10*J4*J2^5 + J6*J4^2*J2^5 + J6*J5*J3*J2^5 + 2*J8*J3^2*J2^5 + J4^2*J3^2*J2^5 + J5*J3^3*J2^5 +
	 J12*J2^6 + J7*J5*J2^6 + J9*J3*J2^6 + 2*J5*J4*J3*J2^6 + J6*J3^2*J2^6 + 2*J3^4*J2^6 + J7*J3*J2^7 + 2*J8*J2^8 +
	 2*J5*J3*J2^8 + 2*J6*J2^9 + 2*J3^2*J2^9 + J4*J2^10 + J2^12 eq 0 and
	 J8*J6*J5^2 + 2*J9*J6*J5*J4 + 2*J5^4*J4 + 2*J9*J7*J4^2 + J7*J5*J4^3 + J8^2*J5*J3 + 2*J7*J6*J4^2*J3 +
	 2*J9*J4^3*J3 + J5*J4^4*J3 + J8*J6*J4*J3^2 + J9*J5*J4*J3^2 + 2*J10*J4^2*J3^2 + 2*J6*J4^3*J3^2 + J6*J5*J4*J3^3 +
	 2*J8*J4*J3^4 + J4^3*J3^4 + 2*J5*J4*J3^5 + 2*J9*J7*J6*J2 + 2*J8*J5^2*J4*J2 + J9*J5*J4^2*J2 + J10*J4^3*J2 +
	 2*J5^2*J4^3*J2 + J10*J5*J4*J3*J2 + 2*J6*J5*J4^2*J3*J2 + J7*J4^3*J3*J2 + J9*J7*J3^2*J2 + J12*J4*J3^2*J2 +
	 2*J8*J4^2*J3^2*J2 + 2*J7*J6*J3^3*J2 + J5*J4^2*J3^3*J2 + J5^2*J3^4*J2 + J7*J3^5*J2 + J4*J3^6*J2 + J9*J6*J5*J2^2
	 + J5^4*J2^2 + 2*J8^2*J4*J2^2 + J9*J7*J4*J2^2 + J7*J5*J4^2*J2^2 + 2*J8*J4^3*J2^2 + J9*J8*J3*J2^2 +
	 J12*J5*J3*J2^2 + 2*J7*J5^2*J3*J2^2 + J7*J6*J4*J3*J2^2 + J9*J4^2*J3*J2^2 + 2*J8*J6*J3^2*J2^2 +
	 J5^2*J4*J3^2*J2^2 + 2*J6*J4^2*J3^2*J2^2 + J6*J5*J3^3*J2^2 + 2*J7*J4*J3^3*J2^2 + 2*J8*J3^4*J2^2 +
	 2*J4^2*J3^4*J2^2 + 2*J5*J3^5*J2^2 + J12*J6*J2^3 + J8*J6*J4*J2^3 + J9*J5*J4*J2^3 + J5^2*J4^2*J2^3 +
	 2*J6*J4^3*J2^3 + J9*J6*J3*J2^3 + 2*J10*J5*J3*J2^3 + 2*J5^3*J3*J2^3 + J6*J5*J4*J3*J2^3 + J7*J4^2*J3*J2^3 +
	 J7*J5*J3^2*J2^3 + J4^3*J3^2*J2^3 + J5*J4*J3^3*J2^3 + 2*J6*J3^4*J2^3 + J8^2*J2^4 + J9*J7*J2^4 + 2*J6*J5^2*J2^4
	 + J7*J5*J4*J2^4 + J8*J4^2*J2^4 + J4^4*J2^4 + J8*J5*J3*J2^4 + J5*J4^2*J3*J2^4 + 2*J10*J3^2*J2^4 +
	 J6*J4*J3^2*J2^4 + J7*J3^3*J2^4 + 2*J4*J3^4*J2^4 + J7^2*J2^5 + 2*J8*J6*J2^5 + J9*J5*J2^5 + J10*J4*J2^5 +
	 2*J5^2*J4*J2^5 + J6*J4^2*J2^5 + 2*J6*J5*J3*J2^5 + 2*J8*J3^2*J2^5 + 2*J12*J2^6 + J9*J3*J2^6 + J3^4*J2^6 +
	 J5^2*J2^7 + J6*J4*J2^7 + 2*J7*J3*J2^7 + J4*J3^2*J2^7 + J8*J2^8 + 2*J6*J2^9 + J3^2*J2^9 + 2*J4*J2^10 eq 0 and
	 J12*J8*J4 + J9*J6*J5*J4 + 2*J12*J4^3 + 2*J8*J4^4 + J4^6 + 2*J12*J5*J4*J3 + J7*J6*J4^2*J3 + J8*J5*J4^2*J3 +
	 J8*J6*J4*J3^2 + 2*J9*J5*J4*J3^2 + 2*J5^2*J4^2*J3^2 + J6*J5*J4*J3^3 + 2*J7*J4^2*J3^3 + 2*J4^3*J3^4 + J5*J4*J3^5
	 + 2*J9*J7*J6*J2 + 2*J12*J5^2*J2 + 2*J8*J5^2*J4*J2 + 2*J9*J5*J4^2*J2 + 2*J10*J4^3*J2 + 2*J5^2*J4^3*J2 +
	 J8*J6*J5*J3*J2 + 2*J9*J5^2*J3*J2 + 2*J9*J6*J4*J3*J2 + J6*J5*J4^2*J3*J2 + J9*J7*J3^2*J2 + J6*J5^2*J3^2*J2 +
	 J12*J4*J3^2*J2 + J7*J5*J4*J3^2*J2 + 2*J8*J4^2*J3^2*J2 + J4^4*J3^2*J2 + 2*J7*J6*J3^3*J2 + 2*J8*J5*J3^3*J2 +
	 J9*J4*J3^3*J2 + 2*J5^2*J3^4*J2 + J7*J3^5*J2 + J4*J3^6*J2 + J9*J6*J5*J2^2 + 2*J5^4*J2^2 + J8^2*J4*J2^2 +
	 J12*J4^2*J2^2 + J9*J8*J3*J2^2 + 2*J12*J5*J3*J2^2 + 2*J7*J5^2*J3*J2^2 + J7*J6*J4*J3*J2^2 + 2*J9*J4^2*J3*J2^2 +
	 J9*J5*J3^2*J2^2 + J5^2*J4*J3^2*J2^2 + 2*J6*J5*J3^3*J2^2 + 2*J7*J4*J3^3*J2^2 + J8*J3^4*J2^2 + J4^2*J3^4*J2^2 +
	 2*J5*J3^5*J2^2 + J12*J6*J2^3 + 2*J8*J6*J4*J2^3 + J9*J5*J4*J2^3 + J10*J4^2*J2^3 + J9*J6*J3*J2^3 +
	 J10*J5*J3*J2^3 + 2*J6*J5*J4*J3*J2^3 + 2*J7*J4^2*J3*J2^3 + 2*J12*J3^2*J2^3 + J4^3*J3^2*J2^3 + 2*J6*J3^4*J2^3 +
	 2*J3^6*J2^3 + J8^2*J2^4 + J9*J7*J2^4 + 2*J6*J5^2*J2^4 + 2*J12*J4*J2^4 + J7*J5*J4*J2^4 + J8*J4^2*J2^4 +
	 2*J4^4*J2^4 + J7*J6*J3*J2^4 + J8*J5*J3*J2^4 + J9*J4*J3*J2^4 + J5*J4^2*J3*J2^4 + 2*J10*J3^2*J2^4 + J7*J3^3*J2^4
	 + J7^2*J2^5 + 2*J8*J6*J2^5 + J9*J5*J2^5 + 2*J10*J4*J2^5 + J6*J4^2*J2^5 + 2*J7*J4*J3*J2^5 + J8*J3^2*J2^5 +
	 2*J4^2*J3^2*J2^5 + 2*J12*J2^6 + 2*J7*J5*J2^6 + 2*J4^3*J2^6 + J9*J3*J2^6 + J6*J3^2*J2^6 + 2*J6*J4*J2^7 +
	 2*J7*J3*J2^7 + J8*J2^8 + 2*J6*J2^9 + J3^2*J2^9 + 2*J4*J2^10 eq 0 and
	 J8^2*J4^2 + J9*J7*J4^2 + 2*J4^6 + 2*J7*J6*J4^2*J3 + J8*J5*J4^2*J3 + J9*J4^3*J3 + J5*J4^4*J3 + J5^2*J4^2*J3^2 +
	 J7*J4^2*J3^3 + J8*J5^2*J4*J2 + 2*J8*J6*J4^2*J2 + J10*J4^3*J2 + 2*J5^2*J4^3*J2 + J6*J4^4*J2 + 2*J9*J6*J4*J3*J2
	 + 2*J6*J5*J4^2*J3*J2 + 2*J8*J4^2*J3^2*J2 + J9*J4*J3^3*J2 + 2*J8^2*J4*J2^2 + 2*J9*J7*J4*J2^2 + 2*J12*J4^2*J2^2
	 + 2*J12*J5*J3*J2^2 + 2*J7*J5^2*J3*J2^2 + J8*J5*J4*J3*J2^2 + J9*J5*J3^2*J2^2 + J10*J4*J3^2*J2^2 +
	 J6*J4^2*J3^2*J2^2 + J7*J4*J3^3*J2^2 + 2*J4^2*J3^4*J2^2 + 2*J5*J3^5*J2^2 + 2*J8*J5^2*J2^3 + J8*J6*J4*J2^3 +
	 J10*J4^2*J2^3 + 2*J5^2*J4^2*J2^3 + J5^3*J3*J2^3 + 2*J6*J5*J4*J3*J2^3 + 2*J7*J4^2*J3*J2^3 + 2*J7*J5*J3^2*J2^3 +
	 2*J8*J4*J3^2*J2^3 + J4^3*J3^2*J2^3 + J5*J4*J3^3*J2^3 + J12*J4*J2^4 + J7*J5*J4*J2^4 + J8*J4^2*J2^4 +
	 J7*J6*J3*J2^4 + J9*J4*J3*J2^4 + 2*J5*J4^2*J3*J2^4 + 2*J5^2*J3^2*J2^4 + 2*J7*J3^3*J2^4 + J4*J3^4*J2^4 +
	 J10*J4*J2^5 + J6*J4^2*J2^5 + J6*J5*J3*J2^5 + J7*J4*J3*J2^5 + 2*J8*J3^2*J2^5 + 2*J7*J5*J2^6 + 2*J8*J4*J2^6 +
	 2*J4^3*J2^6 + J5*J4*J3*J2^6 + 2*J6*J3^2*J2^6 + 2*J5^2*J2^7 + J6*J4*J2^7 + 2*J4*J3^2*J2^7 + 2*J5*J3*J2^8 +
	 J3^2*J2^9 + 2*J4*J2^10 eq 0 and
	 J8^2*J7 + J8*J5^3 + 2*J9*J6*J4^2 + 2*J10*J5*J4^2 + 2*J5^3*J4^2 + J6*J5*J4^3 + 2*J7*J4^4 + 2*J5^4*J3 +
	 2*J8^2*J4*J3 + 2*J12*J4^2*J3 + 2*J7*J5*J4^2*J3 + J8*J4^3*J3 + J4^5*J3 + 2*J7*J5^2*J3^2 + J9*J4^2*J3^2 +
	 2*J5*J4^3*J3^2 + J5^2*J4*J3^3 + 2*J4^2*J3^5 + J9*J8*J4*J2 + J8*J5*J4^2*J2 + J9*J4^3*J2 + J5*J4^4*J2 +
	 J8*J5^2*J3*J2 + 2*J8*J6*J4*J3*J2 + J9*J5*J4*J3*J2 + J10*J4^2*J3*J2 + 2*J6*J4^3*J3*J2 + 2*J8*J7*J3^2*J2 +
	 2*J10*J5*J3^2*J2 + 2*J5^3*J3^2*J2 + 2*J6*J5*J4*J3^2*J2 + 2*J7*J4^2*J3^2*J2 + J7*J5*J3^3*J2 + J8*J4*J3^3*J2 +
	 2*J4^3*J3^3*J2 + J5*J4*J3^4*J2 + J10*J9*J2^2 + J9*J5^2*J2^2 + J9*J6*J4*J2^2 + 2*J10*J5*J4*J2^2 + J5^3*J4*J2^2
	 + 2*J6*J5*J4^2*J2^2 + 2*J9*J7*J3*J2^2 + 2*J12*J4*J3*J2^2 + 2*J7*J5*J4*J3*J2^2 + J4^4*J3*J2^2 +
	 2*J8*J5*J3^2*J2^2 + J5*J4^2*J3^2*J2^2 + 2*J10*J3^3*J2^2 + 2*J5^2*J3^3*J2^2 + 2*J7*J3^4*J2^2 + 2*J4*J3^5*J2^2 +
	 J7*J5^2*J2^3 + 2*J7*J6*J4*J2^3 + 2*J9*J4^2*J2^3 + J5*J4^3*J2^3 + J8*J6*J3*J2^3 + J5^2*J4*J3*J2^3 +
	 J5*J3^4*J2^3 + 2*J9*J6*J2^4 + 2*J10*J5*J2^4 + 2*J6*J5*J4*J2^4 + J12*J3*J2^4 + J7*J5*J3*J2^4 + J4^3*J3*J2^4 +
	 J9*J3^2*J2^4 + 2*J5*J4*J3^2*J2^4 + 2*J7*J6*J2^5 + J8*J5*J2^5 + 2*J5^2*J3*J2^5 + 2*J6*J4*J3*J2^5 +
	 2*J7*J3^2*J2^5 + 2*J6*J5*J2^6 + J8*J3*J2^6 + 2*J5*J3^2*J2^6 + 2*J9*J2^7 + J5*J4*J2^7 + J3^3*J2^7 + 2*J7*J2^8 +
	 J4*J3*J2^8 eq 0 and
	 J9*J7^2 + J8*J5^3 + 2*J10*J9*J4 + J9*J5^2*J4 + 2*J9*J6*J4^2 + 2*J10*J5*J4^2 + 2*J5^3*J4^2 + J6*J5*J4^3 +
	 J12*J8*J3 + 2*J9*J6*J5*J3 + J8^2*J4*J3 + J12*J4^2*J3 + 2*J7*J5*J4^2*J3 + 2*J8*J4^3*J3 + J4^5*J3 +
	 2*J12*J5*J3^2 + J7*J6*J4*J3^2 + J8*J5*J4*J3^2 + 2*J5*J4^3*J3^2 + J7^2*J3^3 + J8*J6*J3^3 + J9*J5*J3^3 +
	 J10*J4*J3^3 + J4^2*J3^5 + 2*J5*J3^6 + 2*J8^2*J5*J2 + J9*J7*J5*J2 + J9*J8*J4*J2 + J12*J5*J4*J2 +
	 2*J8*J5*J4^2*J2 + 2*J9*J4^3*J2 + 2*J12*J6*J3*J2 + J8*J6*J4*J3*J2 + J9*J5*J4*J3*J2 + 2*J5^2*J4^2*J3*J2 +
	 2*J10*J5*J3^2*J2 + 2*J6*J5*J4*J3^2*J2 + 2*J12*J3^3*J2 + J7*J5*J3^3*J2 + J8*J4*J3^3*J2 + 2*J4^3*J3^3*J2 +
	 J3^7*J2 + 2*J10*J9*J2^2 + J8*J6*J5*J2^2 + J10*J5*J4*J2^2 + 2*J8^2*J3*J2^2 + J9*J7*J3*J2^2 + 2*J6*J5^2*J3*J2^2
	 + 2*J7*J5*J4*J3*J2^2 + 2*J8*J4^2*J3*J2^2 + 2*J7*J6*J3^2*J2^2 + J9*J4*J3^2*J2^2 + 2*J10*J3^3*J2^2 +
	 2*J7*J3^4*J2^2 + 2*J4*J3^5*J2^2 + 2*J12*J5*J2^3 + 2*J7*J5^2*J2^3 + 2*J8*J5*J4*J2^3 + 2*J5*J4^3*J2^3 +
	 J7^2*J3*J2^3 + 2*J8*J6*J3*J2^3 + J9*J5*J3*J2^3 + 2*J10*J4*J3*J2^3 + J6*J5*J3^2*J2^3 + J7*J4*J3^2*J2^3 +
	 J8*J3^3*J2^3 + J4^2*J3^3*J2^3 + J9*J6*J2^4 + J10*J5*J2^4 + 2*J5^3*J2^4 + 2*J6*J5*J4*J2^4 + 2*J7*J4^2*J2^4 +
	 2*J12*J3*J2^4 + 2*J7*J5*J3*J2^4 + 2*J8*J4*J3*J2^4 + J4^3*J3*J2^4 + 2*J9*J3^2*J2^4 + 2*J5*J4*J3^2*J2^4 +
	 2*J6*J3^3*J2^4 + 2*J3^5*J2^4 + 2*J8*J5*J2^5 + J9*J4*J2^5 + J5*J4^2*J2^5 + J10*J3*J2^5 + J6*J4*J3*J2^5 +
	 J6*J5*J2^6 + J7*J4*J2^6 + J4^2*J3*J2^6 + J9*J2^7 + J5*J4*J2^7 + 2*J6*J3*J2^7 eq 0 and
	 J12*J6*J5 + 2*J8*J5^3 + 2*J9*J5^2*J4 + J10*J5*J4^2 + J5^3*J4^2 + J6*J5*J4^3 + J5^4*J3 + 2*J12*J5*J3^2 +
	 2*J8*J5*J4*J3^2 + 2*J5*J4^3*J3^2 + 2*J5^2*J4*J3^3 + J6*J5*J3^4 + 2*J5*J3^6 + J8^2*J5*J2 + J9*J8*J4*J2 +
	 J12*J5*J4*J2 + J8*J5^2*J3*J2 + 2*J8*J6*J4*J3*J2 + 2*J9*J5*J4*J3*J2 + J10*J4^2*J3*J2 + J5^2*J4^2*J3*J2 +
	 J5^3*J3^2*J2 + 2*J6*J5*J4*J3^2*J2 + 2*J7*J4^2*J3^2*J2 + 2*J8*J4*J3^3*J2 + J10*J5*J4*J2^2 + J5^3*J4*J2^2 +
	 2*J6*J5*J4^2*J2^2 + 2*J7*J4^3*J2^2 + 2*J6*J5^2*J3*J2^2 + 2*J12*J4*J3*J2^2 + 2*J7*J5*J4*J3*J2^2 + J4^4*J3*J2^2
	 + 2*J5^2*J3^3*J2^2 + 2*J4*J3^5*J2^2 + J12*J5*J2^3 + 2*J7*J5^2*J2^3 + 2*J7*J6*J4*J2^3 + 2*J8*J5*J4*J2^3 +
	 J9*J4^2*J2^3 + 2*J8*J6*J3*J2^3 + J10*J4*J3*J2^3 + J8*J3^3*J2^3 + J4^2*J3^3*J2^3 + 2*J10*J5*J2^4 + J5^3*J2^4 +
	 J6*J5*J4*J2^4 + J12*J3*J2^4 + J7*J5*J3*J2^4 + 2*J8*J4*J3*J2^4 + 2*J4^3*J3*J2^4 + J3^5*J2^4 + J8*J5*J2^5 +
	 J9*J4*J2^5 + J5*J4^2*J2^5 + 2*J7*J3^2*J2^5 + 2*J6*J5*J2^6 + 2*J7*J4*J2^6 + J4^2*J3*J2^6 + 2*J5*J3^2*J2^6 +
	 J6*J3*J2^7 + J3^3*J2^7 + J4*J3*J2^8 + J3*J2^10 eq 0 and
	 J8*J6*J5*J4 + 2*J9*J6*J4^2 + 2*J10*J5*J4^2 + J8^2*J4*J3 + 2*J7*J5*J4^2*J3 + J4^5*J3 + 2*J7*J6*J4*J3^2 +
	 J9*J4^2*J3^2 + 2*J5*J4^3*J3^2 + J5^2*J4*J3^3 + J7*J4*J3^4 + 2*J12*J5*J4*J2 + 2*J7*J6*J4^2*J2 + 2*J8*J5*J4^2*J2
	 + J9*J4^3*J2 + J5*J4^4*J2 + J12*J6*J3*J2 + 2*J8*J5^2*J3*J2 + J8*J6*J4*J3*J2 + 2*J9*J5*J4*J3*J2 +
	 J10*J4^2*J3*J2 + J5^2*J4^2*J3*J2 + J5^3*J3^2*J2 + 2*J7*J4^2*J3^2*J2 + 2*J12*J3^3*J2 + 2*J8*J4*J3^3*J2 +
	 J4^3*J3^3*J2 + J6*J3^5*J2 + 2*J3^7*J2 + 2*J8*J6*J5*J2^2 + J9*J6*J4*J2^2 + J10*J5*J4*J2^2 + J5^3*J4*J2^2 +
	 J7*J4^3*J2^2 + J8^2*J3*J2^2 + J9*J7*J3*J2^2 + J6*J5^2*J3*J2^2 + 2*J8*J4^2*J3*J2^2 + 2*J4^4*J3*J2^2 +
	 J5*J4^2*J3^2*J2^2 + 2*J10*J3^3*J2^2 + 2*J5^2*J3^3*J2^2 + 2*J6*J4*J3^3*J2^2 + 2*J7*J3^4*J2^2 + 2*J4*J3^5*J2^2 +
	 J12*J5*J2^3 + J7*J6*J4*J2^3 + J8*J5*J4*J2^3 + 2*J9*J4^2*J2^3 + J5*J4^3*J2^3 + J7^2*J3*J2^3 + 2*J8*J6*J3*J2^3 +
	 2*J10*J4*J3*J2^3 + J6*J4^2*J3*J2^3 + 2*J7*J4*J3^2*J2^3 + 2*J8*J3^3*J2^3 + J4^2*J3^3*J2^3 + 2*J5*J3^4*J2^3 +
	 2*J5^3*J2^4 + 2*J6*J5*J4*J2^4 + 2*J7*J4^2*J2^4 + 2*J12*J3*J2^4 + 2*J8*J4*J3*J2^4 + J4^3*J3*J2^4 +
	 2*J9*J3^2*J2^4 + J5*J4*J3^2*J2^4 + 2*J6*J3^3*J2^4 + J3^5*J2^4 + 2*J5*J4^2*J2^5 + 2*J6*J4*J3*J2^5 +
	 2*J7*J3^2*J2^5 + J4*J3^3*J2^5 + J6*J5*J2^6 + J8*J3*J2^6 + 2*J4^2*J3*J2^6 + J5*J4*J2^7 + 2*J6*J3*J2^7 +
	 J5*J2^9 eq 0 and
	 J12*J10 + J9*J7*J6 + 2*J12*J5^2 + J8*J5^2*J4 + J8*J6*J4^2 + 2*J9*J5*J4^2 + J10*J4^3 + 2*J6*J4^4 + 2*J9*J5^2*J3
	 + 2*J9*J6*J4*J3 + J7*J4^3*J3 + 2*J8^2*J3^2 + 2*J9*J7*J3^2 + 2*J12*J4*J3^2 + 2*J7*J6*J3^3 + J9*J4*J3^3 +
	 2*J5*J4^2*J3^3 + J10*J3^4 + J5^2*J3^4 + J7*J3^5 + 2*J4*J3^6 + J9*J6*J5*J2 + J5^4*J2 + 2*J8^2*J4*J2 + J4^5*J2 +
	 J9*J8*J3*J2 + J12*J5*J3*J2 + J7*J6*J4*J3*J2 + J8*J5*J4*J3*J2 + 2*J9*J4^2*J3*J2 + 2*J7^2*J3^2*J2 +
	 J10*J4*J3^2*J2 + J5^2*J4*J3^2*J2 + 2*J6*J4^2*J3^2*J2 + J6*J5*J3^3*J2 + J7*J4*J3^3*J2 + 2*J8*J3^4*J2 +
	 J12*J6*J2^2 + 2*J9*J5*J4*J2^2 + 2*J10*J4^2*J2^2 + 2*J5^2*J4^2*J2^2 + 2*J6*J4^3*J2^2 + 2*J9*J6*J3*J2^2 +
	 2*J10*J5*J3*J2^2 + J5^3*J3*J2^2 + J7*J4^2*J3*J2^2 + 2*J12*J3^2*J2^2 + 2*J7*J5*J3^2*J2^2 + 2*J5*J4*J3^3*J2^2 +
	 J3^6*J2^2 + 2*J8^2*J2^3 + 2*J9*J7*J2^3 + J6*J5^2*J2^3 + J12*J4*J2^3 + J8*J4^2*J2^3 + 2*J4^4*J2^3 +
	 2*J8*J5*J3*J2^3 + 2*J9*J4*J3*J2^3 + J5*J4^2*J3*J2^3 + 2*J10*J3^2*J2^3 + J5^2*J3^2*J2^3 + J7*J3^3*J2^3 +
	 2*J7^2*J2^4 + J8*J6*J2^4 + J9*J5*J2^4 + 2*J10*J4*J2^4 + 2*J5^2*J4*J2^4 + J6*J5*J3*J2^4 + J7*J4*J3*J2^4 +
	 J8*J3^2*J2^4 + 2*J4^2*J3^2*J2^4 + 2*J5*J3^3*J2^4 + J8*J4*J2^5 + J4^3*J2^5 + 2*J5*J4*J3*J2^5 + 2*J3^4*J2^5 +
	 J10*J2^6 + 2*J5^2*J2^6 + J6*J4*J2^6 + J7*J3*J2^6 + J4*J3^2*J2^6 + 2*J8*J2^7 + J5*J3*J2^7 + J3^2*J2^8 +
	 2*J2^11 eq 0 and
	 J8*J7^2 + J8*J6*J4^2 + 2*J9*J5*J4^2 + J10*J4^3 + 2*J5^2*J4^3 + 2*J6*J4^4 + 2*J8*J6*J5*J3 + J10*J5*J4*J3 +
	 2*J5^3*J4*J3 + 2*J6*J5*J4^2*J3 + J7*J5*J4*J3^2 + J8*J4^2*J3^2 + J4^4*J3^2 + J8*J5*J3^3 + J5^4*J2 + J9*J7*J4*J2
	 + 2*J12*J4^2*J2 + 2*J7*J5*J4^2*J2 + 2*J7*J5^2*J3*J2 + 2*J7*J6*J4*J3*J2 + 2*J8*J5*J4*J3*J2 + 2*J9*J4^2*J3*J2 +
	 J5*J4^3*J3*J2 + J7^2*J3^2*J2 + 2*J8*J6*J3^2*J2 + J5^2*J4*J3^2*J2 + 2*J6*J4^2*J3^2*J2 + J7*J4*J3^3*J2 +
	 J8*J3^4*J2 + J12*J6*J2^2 + J8*J6*J4*J2^2 + 2*J10*J4^2*J2^2 + 2*J8*J7*J3*J2^2 + 2*J9*J6*J3*J2^2 + J5^3*J3*J2^2
	 + J6*J5*J4*J3*J2^2 + J7*J4^2*J3*J2^2 + 2*J7*J5*J3^2*J2^2 + 2*J8*J4*J3^2*J2^2 + J4^3*J3^2*J2^2 + J9*J3^3*J2^2 +
	 2*J5*J4*J3^3*J2^2 + 2*J6*J3^4*J2^2 + 2*J3^6*J2^2 + J8^2*J2^3 + 2*J6*J5^2*J2^3 + J12*J4*J2^3 + J7*J5*J4*J2^3 +
	 J8*J4^2*J2^3 + 2*J4^4*J2^3 + J7*J6*J3*J2^3 + 2*J8*J5*J3*J2^3 + J10*J3^2*J2^3 + 2*J6*J4*J3^2*J2^3 +
	 2*J7*J3^3*J2^3 + 2*J4*J3^4*J2^3 + 2*J7^2*J2^4 + 2*J8*J6*J2^4 + 2*J9*J5*J2^4 + J5^2*J4*J2^4 + J6*J4^2*J2^4 +
	 2*J6*J5*J3*J2^4 + J7*J4*J3*J2^4 + J5*J3^3*J2^4 + 2*J12*J2^5 + J8*J4*J2^5 + J4^3*J2^5 + 2*J9*J3*J2^5 +
	 J5*J4*J3*J2^5 + 2*J3^4*J2^5 + J5^2*J2^6 + 2*J6*J4*J2^6 + J7*J3*J2^6 + J4*J3^2*J2^6 + J8*J2^7 + J4^2*J2^7 +
	 2*J6*J2^8 + J3^2*J2^8 + 2*J4*J2^9 eq 0 and
	 J8^2*J6 + J12*J5^2 + 2*J8*J5^2*J4 + 2*J8*J6*J4^2 + 2*J9*J5*J4^2 + J10*J4^3 + J10*J5*J4*J3 + J6*J5*J4^2*J3 +
	 2*J7*J4^3*J3 + 2*J8^2*J3^2 + 2*J6*J5^2*J3^2 + J7*J5*J4*J3^2 + 2*J8*J4^2*J3^2 + 2*J5^2*J3^4 + 2*J12*J8*J2 +
	 J9*J6*J5*J2 + J8^2*J4*J2 + 2*J9*J7*J4*J2 + 2*J12*J4^2*J2 + J4^5*J2 + J12*J5*J3*J2 + 2*J7*J6*J4*J3*J2 +
	 J8*J5*J4*J3*J2 + J5*J4^3*J3*J2 + J8*J6*J3^2*J2 + 2*J9*J5*J3^2*J2 + J10*J4*J3^2*J2 + J5^2*J4*J3^2*J2 +
	 J6*J4^2*J3^2*J2 + J6*J5*J3^3*J2 + 2*J7*J4*J3^3*J2 + J8*J3^4*J2 + J4^2*J3^4*J2 + J12*J6*J2^2 + J8*J5^2*J2^2 +
	 J9*J5*J4*J2^2 + J5^2*J4^2*J2^2 + J6*J4^3*J2^2 + J8*J7*J3*J2^2 + 2*J10*J5*J3*J2^2 + 2*J5^3*J3*J2^2 +
	 J7*J4^2*J3*J2^2 + J12*J3^2*J2^2 + J7*J5*J3^2*J2^2 + 2*J8*J4*J3^2*J2^2 + 2*J4^3*J3^2*J2^2 + J5*J4*J3^3*J2^2 +
	 J6*J3^4*J2^2 + J3^6*J2^2 + J8^2*J2^3 + J9*J7*J2^3 + 2*J6*J5^2*J2^3 + J12*J4*J2^3 + 2*J7*J5*J4*J2^3 +
	 2*J4^4*J2^3 + J7*J6*J3*J2^3 + J8*J5*J3*J2^3 + J9*J4*J3*J2^3 + J5*J4^2*J3*J2^3 + 2*J10*J3^2*J2^3 +
	 2*J7*J3^3*J2^3 + 2*J4*J3^4*J2^3 + J7^2*J2^4 + 2*J9*J5*J2^4 + J5^2*J4*J2^4 + 2*J6*J5*J3*J2^4 + J8*J3^2*J2^4 +
	 2*J4^2*J3^2*J2^4 + 2*J5*J3^3*J2^4 + 2*J7*J5*J2^5 + J8*J4*J2^5 + J4^3*J2^5 + 2*J9*J3*J2^5 + J3^4*J2^5 +
	 J5^2*J2^6 + J7*J3*J2^6 + J4*J3^2*J2^6 + J4^2*J2^7 + J3^2*J2^8 + J4*J2^9 + J2^11 eq 0 and
	 J7*J5^3 + J9*J5*J4^2 + 2*J5^2*J4^3 + J8*J6*J5*J3 + J10*J5*J4*J3 + J6*J5*J4^2*J3 + J6*J5^2*J3^2 + J7*J5*J4*J3^2
	 + 2*J8*J5*J3^3 + 2*J5*J4^2*J3^3 + 2*J5^2*J3^4 + 2*J5^4*J2 + J8^2*J4*J2 + J9*J7*J4*J2 + J7*J5*J4^2*J2 +
	 2*J4^5*J2 + 2*J7*J5^2*J3*J2 + 2*J7*J6*J4*J3*J2 + 2*J8*J5*J4*J3*J2 + 2*J9*J4^2*J3*J2 + 2*J5*J4^3*J3*J2 +
	 2*J10*J4*J3^2*J2 + 2*J5^2*J4*J3^2*J2 + 2*J6*J4^2*J3^2*J2 + J4^2*J3^4*J2 + J8*J5^2*J2^2 + 2*J8*J6*J4*J2^2 +
	 J10*J4^2*J2^2 + J5^2*J4^2*J2^2 + J6*J4^3*J2^2 + 2*J10*J5*J3*J2^2 + 2*J5^3*J3*J2^2 + J7*J4^2*J3*J2^2 +
	 2*J7*J5*J3^2*J2^2 + J4^3*J3^2*J2^2 + J5*J4*J3^3*J2^2 + J6*J5^2*J2^3 + J7*J5*J4*J2^3 + J8*J4^2*J2^3 +
	 2*J4^4*J2^3 + 2*J7*J6*J3*J2^3 + 2*J8*J5*J3*J2^3 + J5*J4^2*J3*J2^3 + 2*J5^2*J3^2*J2^3 + J6*J4*J3^2*J2^3 +
	 J7*J3^3*J2^3 + 2*J4*J3^4*J2^3 + 2*J10*J4*J2^4 + 2*J5^2*J4*J2^4 + J6*J4^2*J2^4 + 2*J6*J5*J3*J2^4 +
	 2*J7*J4*J3*J2^4 + J8*J3^2*J2^4 + 2*J5*J3^3*J2^4 + J7*J5*J2^5 + J8*J4*J2^5 + 2*J4^3*J2^5 + J6*J3^2*J2^5 +
	 2*J5^2*J2^6 + 2*J6*J4*J2^6 + J4^2*J2^7 + 2*J5*J3*J2^7 + 2*J3^2*J2^8 + 2*J4*J2^9 eq 0 and
	 J12*J6*J4 + 2*J8*J5^2*J4 + 2*J9*J5*J4^2 + J10*J4^3 + J5^2*J4^3 + J6*J4^4 + J5^3*J4*J3 + 2*J12*J4*J3^2 +
	 2*J8*J4^2*J3^2 + 2*J4^4*J3^2 + 2*J5*J4^2*J3^3 + J6*J4*J3^4 + 2*J4*J3^6 + J5^4*J2 + 2*J9*J7*J4*J2 +
	 2*J12*J4^2*J2 + 2*J7*J5*J4^2*J2 + 2*J8*J4^3*J2 + J4^5*J2 + J12*J5*J3*J2 + 2*J7*J5^2*J3*J2 + J7*J6*J4*J3*J2 +
	 2*J9*J4^2*J3*J2 + J5*J4^3*J3*J2 + J10*J4*J3^2*J2 + 2*J4^2*J3^4*J2 + J5*J3^5*J2 + J12*J6*J2^2 + 2*J8*J5^2*J2^2
	 + 2*J10*J4^2*J2^2 + J5^2*J4^2*J2^2 + 2*J6*J4^3*J2^2 + 2*J10*J5*J3*J2^2 + J5^3*J3*J2^2 + 2*J6*J5*J4*J3*J2^2 +
	 2*J12*J3^2*J2^2 + J7*J5*J3^2*J2^2 + 2*J4^3*J3^2*J2^2 + J5*J4*J3^3*J2^2 + J6*J3^4*J2^2 + 2*J3^6*J2^2 +
	 J8^2*J2^3 + J9*J7*J2^3 + J6*J5^2*J2^3 + 2*J7*J5*J4*J2^3 + J8*J4^2*J2^3 + J7*J6*J3*J2^3 + 2*J8*J5*J3*J2^3 +
	 J5*J4^2*J3*J2^3 + 2*J10*J3^2*J2^3 + J5^2*J3^2*J2^3 + J6*J4*J3^2*J2^3 + J7*J3^3*J2^3 + J4*J3^4*J2^3 + J7^2*J2^4
	 + 2*J8*J6*J2^4 + J9*J5*J2^4 + J5^2*J4*J2^4 + 2*J6*J4^2*J2^4 + 2*J6*J5*J3*J2^4 + J8*J3^2*J2^4 + J4^2*J3^2*J2^4
	 + J5*J3^3*J2^4 + 2*J12*J2^5 + J7*J5*J2^5 + J8*J4*J2^5 + 2*J9*J3*J2^5 + 2*J5*J4*J3*J2^5 + J6*J3^2*J2^5 +
	 J3^4*J2^5 + 2*J5^2*J2^6 + J6*J4*J2^6 + 2*J7*J3*J2^6 + 2*J4*J3^2*J2^6 + J8*J2^7 + 2*J6*J2^8 + J3^2*J2^8 +
	 J4*J2^9 eq 0 and
	 J7^3 + J7*J6*J4^2 + J8*J5*J4^2 + J5*J4^4 + J8*J6*J4*J3 + J10*J4^2*J3 + J6*J4^3*J3 + 2*J5^3*J3^2 +
	 J6*J5*J4*J3^2 + 2*J8*J4*J3^3 + 2*J4^3*J3^3 + 2*J5*J4*J3^4 + J10*J5*J4*J2 + J5^3*J4*J2 + 2*J6*J5*J4^2*J2 +
	 2*J6*J5^2*J3*J2 + J12*J4*J3*J2 + 2*J7*J5*J4*J3*J2 + J4^4*J3*J2 + J8*J5*J3^2*J2 + 2*J5^2*J3^3*J2 + J4*J3^5*J2 +
	 2*J7*J5^2*J2^2 + J8*J5*J4*J2^2 + 2*J9*J4^2*J2^2 + 2*J5*J4^3*J2^2 + J7^2*J3*J2^2 + J5^2*J4*J3*J2^2 +
	 J6*J4^2*J3*J2^2 + J7*J4*J3^2*J2^2 + 2*J4^2*J3^3*J2^2 + J8*J7*J2^3 + 2*J10*J5*J2^3 + 2*J5^3*J2^3 +
	 2*J7*J4^2*J2^3 + J12*J3*J2^3 + J8*J4*J3*J2^3 + J4^3*J3*J2^3 + 2*J9*J3^2*J2^3 + 2*J5*J4*J3^2*J2^3 +
	 2*J6*J3^3*J2^3 + J7*J6*J2^4 + 2*J8*J5*J2^4 + J9*J4*J2^4 + J5*J4^2*J2^4 + 2*J10*J3*J2^4 + 2*J7*J3^2*J2^4 +
	 J4*J3^3*J2^4 + 2*J7*J4*J2^5 + 2*J8*J3*J2^5 + J5*J3^2*J2^5 + J3^3*J2^6 + 2*J7*J2^7 + 2*J4*J3*J2^7 + 2*J5*J2^8 eq 0 and
	 J8*J7*J6 + 2*J12*J5*J4 + J7*J6*J4^2 + 2*J9*J4^3 + J5*J4^4 + 2*J8*J5^2*J3 + J8*J6*J4*J3 + J10*J4^2*J3 +
	 J6*J4^3*J3 + 2*J8*J7*J3^2 + J6*J5*J4*J3^2 + 2*J8*J4*J3^3 + 2*J4^3*J3^3 + J5*J4*J3^4 + J8*J6*J5*J2 +
	 2*J10*J5*J4*J2 + J5^3*J4*J2 + J6*J5*J4^2*J2 + 2*J8^2*J3*J2 + J6*J5^2*J3*J2 + 2*J12*J4*J3*J2 + J7*J5*J4*J3*J2 +
	 2*J4^4*J3*J2 + J7*J6*J3^2*J2 + J8*J5*J3^2*J2 + 2*J5*J4^2*J3^2*J2 + 2*J5^2*J3^3*J2 + 2*J7*J3^4*J2 +
	 2*J4*J3^5*J2 + J12*J5*J2^2 + J7*J5^2*J2^2 + J7*J6*J4*J2^2 + 2*J8*J5*J4*J2^2 + 2*J5*J4^3*J2^2 + J9*J5*J3*J2^2 +
	 2*J10*J4*J3*J2^2 + J5^2*J4*J3*J2^2 + 2*J6*J4^2*J3*J2^2 + 2*J6*J5*J3^2*J2^2 + J7*J4*J3^2*J2^2 + J8*J3^3*J2^2 +
	 2*J4^2*J3^3*J2^2 + 2*J10*J5*J2^3 + 2*J6*J5*J4*J2^3 + 2*J12*J3*J2^3 + J7*J5*J3*J2^3 + 2*J8*J4*J3*J2^3 +
	 2*J4^3*J3*J2^3 + J5*J4*J3^2*J2^3 + 2*J6*J3^3*J2^3 + 2*J3^5*J2^3 + 2*J7*J6*J2^4 + J9*J4*J2^4 + 2*J5*J4^2*J2^4 +
	 J5^2*J3*J2^4 + 2*J7*J3^2*J2^4 + J7*J4*J2^5 + 2*J8*J3*J2^5 + J5*J3^2*J2^5 + J5*J4*J2^6 + 2*J4*J3*J2^7 +
	 2*J5*J2^8 + J3*J2^9 eq 0 and
	 J6*J5^3 + J12*J5*J4 + J8*J5*J4^2 + 2*J9*J4^3 + J5*J4^4 + J8*J5^2*J3 + J10*J4^2*J3 + J5^2*J4^2*J3 + J6*J4^3*J3
	 + J7*J4^2*J3^2 + 2*J4^3*J3^3 + J5*J4*J3^4 + J8*J6*J5*J2 + 2*J9*J6*J4*J2 + 2*J10*J5*J4*J2 + 2*J5^3*J4*J2 +
	 2*J7*J4^3*J2 + J6*J5^2*J3*J2 + J7*J5*J4*J3*J2 + 2*J8*J4^2*J3*J2 + 2*J4^4*J3*J2 + 2*J8*J5*J3^2*J2 +
	 J9*J4*J3^2*J2 + 2*J5*J4^2*J3^2*J2 + 2*J5^2*J3^3*J2 + 2*J12*J5*J2^2 + J7*J5^2*J2^2 + 2*J7*J6*J4*J2^2 +
	 2*J8*J5*J4*J2^2 + 2*J9*J4^2*J2^2 + J5*J4^3*J2^2 + J9*J5*J3*J2^2 + 2*J6*J4^2*J3*J2^2 + J7*J4*J3^2*J2^2 +
	 2*J4^2*J3^3*J2^2 + 2*J5*J3^4*J2^2 + J5^3*J2^3 + 2*J7*J4^2*J2^3 + 2*J7*J5*J3*J2^3 + 2*J4^3*J3*J2^3 +
	 2*J5*J4*J3^2*J2^3 + J5*J4^2*J2^4 + J6*J4*J3*J2^4 + 2*J4*J3^3*J2^4 + 2*J6*J5*J2^5 + J4^2*J3*J2^5 + J5*J3^2*J2^5
	 + 2*J5*J4*J2^6 + 2*J5*J2^8 eq 0 and
	 J7*J5^2*J4 + J9*J4^3 + 2*J5*J4^4 + J8*J6*J4*J3 + J10*J4^2*J3 + J6*J4^3*J3 + J6*J5*J4*J3^2 + J7*J4^2*J3^2 +
	 2*J8*J4*J3^3 + 2*J4^3*J3^3 + 2*J5*J4*J3^4 + 2*J5^3*J4*J2 + J7*J4^3*J2 + J6*J5^2*J3*J2 + J12*J4*J3*J2 +
	 2*J7*J5*J4*J3*J2 + 2*J8*J4^2*J3*J2 + 2*J4^4*J3*J2 + J8*J5*J3^2*J2 + 2*J5*J4^2*J3^2*J2 + J4*J3^5*J2 +
	 2*J7*J5^2*J2^2 + 2*J9*J4^2*J2^2 + J5^2*J4*J3*J2^2 + 2*J7*J4*J3^2*J2^2 + J4^2*J3^3*J2^2 + J5^3*J2^3 +
	 2*J7*J4^2*J2^3 + 2*J4^3*J3*J2^3 + 2*J5*J4*J3^2*J2^3 + J5*J4^2*J2^4 + 2*J5^2*J3*J2^4 + 2*J6*J4*J3*J2^4 +
	 2*J4^2*J3*J2^5 + 2*J5*J3^2*J2^5 + J4*J3*J2^7 eq 0 and
	 J10^2 + J5^4 + J8^2*J4 + 2*J9*J7*J4 + J12*J4^2 + 2*J12*J5*J3 + J7*J5^2*J3 + J7*J6*J4*J3 + J5*J4^3*J3 +
	 2*J7^2*J3^2 + J8*J6*J3^2 + 2*J5^2*J4*J3^2 + J6*J5*J3^3 + 2*J7*J4*J3^3 + 2*J8*J3^4 + J4^2*J3^4 + J5*J3^5 +
	 2*J12*J6*J2 + J8*J5^2*J2 + J8*J6*J4*J2 + J9*J5*J4*J2 + J5^2*J4^2*J2 + J6*J4^3*J2 + 2*J8*J7*J3*J2 + J9*J6*J3*J2
	 + 2*J10*J5*J3*J2 + J5^3*J3*J2 + 2*J12*J3^2*J2 + J7*J5*J3^2*J2 + J4^3*J3^2*J2 + 2*J9*J3^3*J2 + J5*J4*J3^3*J2 +
	 2*J6*J3^4*J2 + 2*J3^6*J2 + 2*J8^2*J2^2 + J12*J4*J2^2 + J7*J5*J4*J2^2 + 2*J8*J4^2*J2^2 + J8*J5*J3*J2^2 +
	 J9*J4*J3*J2^2 + J5*J4^2*J3*J2^2 + J6*J4*J3^2*J2^2 + J9*J5*J2^3 + J6*J4^2*J2^3 + J7*J4*J3*J2^3 + J8*J3^2*J2^3 +
	 J5*J3^3*J2^3 + 2*J12*J2^4 + J7*J5*J2^4 + 2*J8*J4*J2^4 + J4^3*J2^4 + 2*J9*J3*J2^4 + 2*J6*J3^2*J2^4 +
	 2*J3^4*J2^4 + 2*J10*J2^5 + J6*J4*J2^5 + 2*J4*J3^2*J2^5 + 2*J6*J2^7 + 2*J3^2*J2^7 + J4*J2^8 eq 0 and
	 J7^2*J6 + J12*J4^2 + J7*J5*J4^2 + 2*J8*J4^3 + 2*J4^5 + 2*J7*J5^2*J3 + J8*J5*J4*J3 + 2*J7^2*J3^2 + J5^2*J4*J3^2
	 + J4^2*J3^4 + 2*J8*J6*J4*J2 + 2*J10*J4^2*J2 + 2*J5^2*J4^2*J2 + J6*J4^3*J2 + 2*J8*J7*J3*J2 + 2*J10*J5*J3*J2 +
	 2*J5^3*J3*J2 + J6*J5*J4*J3*J2 + J8*J4*J3^2*J2 + J4^3*J3^2*J2 + 2*J5*J4*J3^3*J2 + 2*J12*J4*J2^2 +
	 2*J7*J5*J4*J2^2 + 2*J4^4*J2^2 + 2*J7*J6*J3*J2^2 + J8*J5*J3*J2^2 + 2*J9*J4*J3*J2^2 + J5^2*J3^2*J2^2 +
	 J6*J4*J3^2*J2^2 + J4*J3^4*J2^2 + 2*J5^2*J4*J2^3 + 2*J7*J4*J3*J2^3 + 2*J4^2*J3^2*J2^3 + 2*J5*J4*J3*J2^4 +
	 J5^2*J2^5 + J6*J4*J2^5 + J7*J3*J2^5 + J4*J3^2*J2^5 + J4^2*J2^6 + 2*J4*J2^8 eq 0 and
	 J8*J7*J5 + J5^4 + J12*J4^2 + 2*J7*J5*J4^2 + J8*J4^3 + J7*J5^2*J3 + 2*J7*J6*J4*J3 + 2*J8*J5*J4*J3 + J5*J4^3*J3
	 + J7*J4*J3^3 + J4^2*J3^4 + J12*J6*J2 + 2*J8*J5^2*J2 + 2*J8*J6*J4*J2 + 2*J10*J4^2*J2 + J5^2*J4^2*J2 +
	 2*J6*J4^3*J2 + 2*J10*J5*J3*J2 + 2*J7*J4^2*J3*J2 + 2*J12*J3^2*J2 + 2*J7*J5*J3^2*J2 + 2*J8*J4*J3^2*J2 +
	 J4^3*J3^2*J2 + 2*J5*J4*J3^3*J2 + J6*J3^4*J2 + 2*J3^6*J2 + J8^2*J2^2 + J9*J7*J2^2 + 2*J6*J5^2*J2^2 +
	 2*J12*J4*J2^2 + 2*J8*J4^2*J2^2 + J4^4*J2^2 + J8*J5*J3*J2^2 + 2*J9*J4*J3*J2^2 + J5*J4^2*J3*J2^2 +
	 2*J10*J3^2*J2^2 + 2*J6*J4*J3^2*J2^2 + 2*J7*J3^3*J2^2 + J4*J3^4*J2^2 + J7^2*J2^3 + 2*J8*J6*J2^3 + J9*J5*J2^3 +
	 2*J10*J4*J2^3 + 2*J5^2*J4*J2^3 + J6*J5*J3*J2^3 + 2*J7*J4*J3*J2^3 + 2*J8*J3^2*J2^3 + J4^2*J3^2*J2^3 +
	 2*J5*J3^3*J2^3 + 2*J12*J2^4 + J7*J5*J2^4 + J8*J4*J2^4 + 2*J4^3*J2^4 + 2*J9*J3*J2^4 + 2*J6*J3^2*J2^4 +
	 J3^4*J2^4 + 2*J5^2*J2^5 + 2*J6*J4*J2^5 + 2*J7*J3*J2^5 + J8*J2^6 + 2*J6*J2^7 + J4*J2^8 eq 0 and
	 J10*J5^2 + 2*J5^4 + J8^2*J4 + J7*J5*J4^2 + 2*J4^5 + J7*J5^2*J3 + J7*J6*J4*J3 + J8*J5*J4*J3 + J5*J4^3*J3 +
	 2*J5^2*J4*J3^2 + 2*J7*J4*J3^3 + J12*J6*J2 + J8*J5^2*J2 + 2*J8*J6*J4*J2 + J5^2*J4^2*J2 + 2*J6*J4^3*J2 +
	 J10*J5*J3*J2 + 2*J6*J5*J4*J3*J2 + 2*J7*J4^2*J3*J2 + 2*J12*J3^2*J2 + J7*J5*J3^2*J2 + 2*J5*J4*J3^3*J2 +
	 J6*J3^4*J2 + 2*J3^6*J2 + J8^2*J2^2 + J9*J7*J2^2 + J6*J5^2*J2^2 + 2*J8*J4^2*J2^2 + 2*J4^4*J2^2 + J8*J5*J3*J2^2
	 + J5*J4^2*J3*J2^2 + 2*J10*J3^2*J2^2 + 2*J7*J3^3*J2^2 + 2*J4*J3^4*J2^2 + J7^2*J2^3 + 2*J8*J6*J2^3 + J9*J5*J2^3
	 + 2*J10*J4*J2^3 + 2*J5^2*J4*J2^3 + 2*J6*J4^2*J2^3 + 2*J6*J5*J3*J2^3 + 2*J7*J4*J3*J2^3 + 2*J8*J3^2*J2^3 +
	 J4^2*J3^2*J2^3 + 2*J12*J2^4 + 2*J7*J5*J2^4 + 2*J8*J4*J2^4 + 2*J9*J3*J2^4 + 2*J6*J3^2*J2^4 + J3^4*J2^4 +
	 2*J5^2*J2^5 + 2*J6*J4*J2^5 + 2*J7*J3*J2^5 + J8*J2^6 + 2*J4^2*J2^6 + J5*J3*J2^6 + 2*J6*J2^7 eq 0 and
	 J6*J5^2*J4 + J12*J4^2 + J7*J5*J4^2 + J8*J4^3 + 2*J7*J6*J4*J3 + J8*J5*J4*J3 + J5*J4^3*J3 + J5^2*J4*J3^2 +
	 J7*J4*J3^3 + J4^2*J3^4 + J5^2*J4^2*J2 + J10*J5*J3*J2 + 2*J5^3*J3*J2 + J6*J5*J4*J3*J2 + J7*J4^2*J3*J2 +
	 J7*J5*J3^2*J2 + 2*J8*J4*J3^2*J2 + 2*J5*J4*J3^3*J2 + 2*J6*J5^2*J2^2 + 2*J12*J4*J2^2 + 2*J7*J5*J4*J2^2 +
	 2*J8*J4^2*J2^2 + J8*J5*J3*J2^2 + 2*J9*J4*J3*J2^2 + 2*J5*J4^2*J3*J2^2 + J6*J4*J3^2*J2^2 + 2*J4*J3^4*J2^2 +
	 2*J6*J5*J3*J2^3 + J4^2*J3^2*J2^3 + 2*J5*J3^3*J2^3 + 2*J5*J4*J3*J2^4 + 2*J5^2*J2^5 + J4^2*J2^6 + J5*J3*J2^6 +
	 2*J4*J2^8 eq 0 and
	 J12*J7 + J8*J6*J5 + J9*J6*J4 + J10*J5*J4 + 2*J6*J5*J4^2 + 2*J7*J4^3 + 2*J8^2*J3 + J6*J5^2*J3 + J12*J4*J3 +
	 J7*J5*J4*J3 + J8*J4^2*J3 + J4^4*J3 + J7*J6*J3^2 + J8*J5*J3^2 + 2*J9*J4*J3^2 + J5*J4^2*J3^2 + J5^2*J3^3 +
	 J4*J3^5 + J12*J5*J2 + J7*J5^2*J2 + 2*J9*J4^2*J2 + 2*J7^2*J3*J2 + 2*J8*J6*J3*J2 + 2*J9*J5*J3*J2 + J5^2*J4*J3*J2
	 + 2*J7*J4*J3^2*J2 + 2*J8*J3^3*J2 + J4^2*J3^3*J2 + J5*J3^4*J2 + J10*J5*J2^2 + J5^3*J2^2 + J7*J4^2*J2^2 +
	 J7*J5*J3*J2^2 + 2*J8*J4*J3*J2^2 + 2*J4^3*J3*J2^2 + 2*J6*J3^3*J2^2 + 2*J5*J4^2*J2^3 + 2*J5^2*J3*J2^3 +
	 2*J6*J4*J3*J2^3 + 2*J7*J3^2*J2^3 + 2*J4*J3^3*J2^3 + J6*J5*J2^4 + J7*J4*J2^4 + 2*J8*J3*J2^4 + J4^2*J3*J2^4 +
	 J5*J3^2*J2^4 + J6*J3*J2^5 + J3^3*J2^5 + J7*J2^6 + 2*J4*J3*J2^6 + 2*J3*J2^8 eq 0 and
	 J7^2*J5 + J10*J5*J4 + 2*J5^3*J4 + 2*J6*J5^2*J3 + J7*J5*J4*J3 + J5^2*J3^3 + J8*J5*J4*J2 + 2*J9*J4^2*J2 +
	 J5*J4^3*J2 + J8*J6*J3*J2 + J5^2*J4*J3*J2 + 2*J6*J5*J3^2*J2 + 2*J8*J3^3*J2 + J5*J3^4*J2 + J10*J5*J2^2 +
	 2*J6*J5*J4*J2^2 + 2*J7*J4^2*J2^2 + 2*J12*J3*J2^2 + J7*J5*J3*J2^2 + J8*J4*J3*J2^2 + 2*J4^3*J3*J2^2 +
	 2*J5*J4*J3^2*J2^2 + 2*J3^5*J2^2 + J9*J4*J2^3 + 2*J5*J4^2*J2^3 + J6*J4*J3*J2^3 + J7*J3^2*J2^3 + J4*J3^3*J2^3 +
	 2*J6*J5*J2^4 + J7*J4*J2^4 + J4^2*J3*J2^4 + 2*J5*J3^2*J2^4 + 2*J6*J3*J2^5 + 2*J3^3*J2^5 + 2*J5*J2^7 +
	 2*J3*J2^8 eq 0 and
	 J8*J7*J4 + J5^3*J4 + 2*J6*J5*J4^2 + J7*J4^3 + J7*J5*J4*J3 + J8*J4^2*J3 + 2*J5*J4^2*J3^2 + J7*J5^2*J2 +
	 J7*J6*J4*J2 + 2*J9*J4^2*J2 + J5*J4^3*J2 + J8*J6*J3*J2 + 2*J10*J4*J3*J2 + 2*J5^2*J4*J3*J2 + J6*J4^2*J3*J2 +
	 J6*J5*J3^2*J2 + J7*J4*J3^2*J2 + 2*J8*J3^3*J2 + 2*J4^2*J3^3*J2 + 2*J5*J3^4*J2 + J10*J5*J2^2 + 2*J6*J5*J4*J2^2 +
	 2*J12*J3*J2^2 + J7*J5*J3*J2^2 + 2*J4^3*J3*J2^2 + 2*J3^5*J2^2 + J9*J4*J2^3 + 2*J5^2*J3*J2^3 + J6*J4*J3*J2^3 +
	 J7*J3^2*J2^3 + 2*J4*J3^3*J2^3 + 2*J6*J5*J2^4 + 2*J4^2*J3*J2^4 + 2*J5*J3^2*J2^4 + 2*J5*J4*J2^5 + 2*J6*J3*J2^5 +
	 2*J3^3*J2^5 + 2*J4*J3*J2^6 + 2*J5*J2^7 + 2*J3*J2^8 eq 0 and
	 J10*J8 + 2*J12*J6 + 2*J8*J6*J4 + 2*J9*J5*J4 + J10*J4^2 + 2*J8*J7*J3 + 2*J10*J5*J3 + J5^3*J3 + J7*J4^2*J3 +
	 J12*J3^2 + J8*J4*J3^2 + 2*J6*J3^4 + J3^6 + 2*J8^2*J2 + J9*J7*J2 + J6*J5^2*J2 + 2*J12*J4*J2 + J7*J5*J4*J2 +
	 J8*J4^2*J2 + J4^4*J2 + 2*J7*J6*J3*J2 + 2*J8*J5*J3*J2 + J9*J4*J3*J2 + J5*J4^2*J3*J2 + 2*J10*J3^2*J2 +
	 2*J5^2*J3^2*J2 + 2*J6*J4*J3^2*J2 + J7^2*J2^2 + 2*J8*J6*J2^2 + 2*J9*J5*J2^2 + 2*J5^2*J4*J2^2 + 2*J6*J4^2*J2^2 +
	 2*J6*J5*J3*J2^2 + J8*J3^2*J2^2 + 2*J4^2*J3^2*J2^2 + 2*J5*J3^3*J2^2 + 2*J12*J2^3 + J4^3*J2^3 + 2*J9*J3*J2^3 +
	 J6*J3^2*J2^3 + 2*J3^4*J2^3 + 2*J10*J2^4 + J8*J2^5 + 2*J4^2*J2^5 + J5*J3*J2^5 + J4*J2^7 + 2*J2^9 eq 0 and
	 J7*J6*J5 + J8*J6*J4 + 2*J10*J4^2 + 2*J6*J4^3 + 2*J5^3*J3 + J6*J5*J4*J3 + 2*J7*J4^2*J3 + 2*J7*J5*J3^2 +
	 2*J8*J4*J3^2 + J4^3*J3^2 + 2*J5*J4*J3^3 + 2*J4^4*J2 + J8*J5*J3*J2 + 2*J5*J4^2*J3*J2 + 2*J6*J4^2*J2^2 +
	 2*J6*J5*J3*J2^2 + J4^2*J3^2*J2^2 + J5^2*J2^4 + 2*J6*J4*J2^4 + J4*J3^2*J2^4 + J4^2*J2^5 + 2*J5*J3*J2^5 eq 0 and
	 J7^2*J4 + J10*J4^2 + 2*J5^2*J4^2 + 2*J6*J5*J4*J3 + J7*J4^2*J3 + J5*J4*J3^3 + J7*J5*J4*J2 + J8*J4^2*J2 +
	 J7*J6*J3*J2 + J5*J4^2*J3*J2 + 2*J5^2*J3^2*J2 + J6*J4*J3^2*J2 + 2*J7*J3^3*J2 + 2*J4*J3^4*J2 + J10*J4*J2^2 +
	 2*J5^2*J4*J2^2 + 2*J6*J4^2*J2^2 + J6*J5*J3*J2^2 + 2*J8*J3^2*J2^2 + 2*J7*J5*J2^3 + 2*J4^3*J2^3 + J5*J4*J3*J2^3
	 + 2*J6*J3^2*J2^3 + J5^2*J2^4 + 2*J6*J4*J2^4 + J4*J3^2*J2^4 + J4^2*J2^5 + J3^2*J2^6 + 2*J4*J2^7 eq 0 and
	 J10*J7 + J7*J5^2 + 2*J7*J6*J4 + 2*J8*J5*J4 + 2*J9*J4^2 + 2*J7^2*J3 + 2*J8*J6*J3 + J10*J4*J3 + 2*J5^2*J4*J3 +
	 J6*J5*J3^2 + 2*J7*J4*J3^2 + J8*J3^3 + 2*J5*J3^4 + J8*J7*J2 + J10*J5*J2 + J5^3*J2 + J6*J5*J4*J2 + 2*J7*J4^2*J2
	 + 2*J12*J3*J2 + J7*J5*J3*J2 + 2*J8*J4*J3*J2 + J6*J3^3*J2 + J3^5*J2 + 2*J8*J5*J2^2 + J9*J4*J2^2 + 2*J10*J3*J2^2
	 + J7*J3^2*J2^2 + 2*J4*J3^3*J2^2 + J6*J5*J2^3 + 2*J7*J4*J2^3 + 2*J8*J3*J2^3 + 2*J4^2*J3*J2^3 + J5*J3^2*J2^3 +
	 2*J5*J4*J2^4 + J6*J3*J2^4 + J3^3*J2^4 + J7*J2^5 + J3*J2^7 eq 0 and
	 J10*J6 + J6*J5^2 + J12*J4 + J7*J5*J4 + J4^4 + 2*J7*J6*J3 + 2*J8*J5*J3 + 2*J5*J4^2*J3 + 2*J10*J3^2 + J7*J3^3 +
	 J4*J3^4 + J8*J6*J2 + 2*J10*J4*J2 + J6*J5*J3*J2 + 2*J8*J3^2*J2 + J4^2*J3^2*J2 + J5*J3^3*J2 + 2*J12*J2^2 +
	 J7*J5*J2^2 + J4^3*J2^2 + 2*J9*J3*J2^2 + 2*J5*J4*J3*J2^2 + J3^4*J2^2 + J10*J2^3 + J5^2*J2^3 + 2*J6*J4*J2^3 +
	 2*J7*J3*J2^3 + J8*J2^4 + 2*J4^2*J2^4 + J6*J2^5 + 2*J4*J2^6 eq 0 and
	 J6^2 + 2*J7*J5 + J8*J4 + J5*J4*J3 + J6*J3^2 + J3^4 + J10*J2 + 2*J5^2*J2 + 2*J7*J3*J2 + J8*J2^2 + J4^2*J2^2 +
	 J5*J3*J2^2 + 2*J3^2*J2^3 + J2^6 eq 0
	then
	 vprintf G3Twists, 1 : "Automorphism group D2, curve y^2 = (x^2-1)*(x^6+a*x^4+b*x^2+c)\n";
	 aut:= SmallGroup(4, 2);
	 if models then twists:= G3Char3Models_D2(JI: geometric:= geometric); end if;
	 return twists, aut;
     end if;


     /*** General case ***/
     vprintf G3Twists, 1 : "Automorphism group C2 \n";
     aut:= CyclicGroup(2);
     f:= Genus3Char3ConicAndQuartic(JI : models:= models);
     if models then
	 error if Type(f) eq BoolElt, "[G3Twists] None C2-model found !\n(do invariants satisfy algebraic relations ?)";
	 twists:= [f];
     end if;
     if geometric or not models then return twists, aut; end if;
     return [f, PrimitiveElement(FF)*f], aut;

 end function;




