//freeze;

/***
 *  Reconstruction of genus 3 hyperelliptic curves with automorphism group
 *  equal to D2 in characteristic 3.
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
 *  Copyright 2013, R. Basson, R. Lercier, C. Ritzenthaler & J. Sijsling
 */


 import "conic.m"       : FindPointOnConic;

 /* Case D2
   y^2 = a8 * x^8 + a6 * x^6 + a4 * x^4 + a2 * x^2 + a0;
*/
function G3Char3Models_D2(JI : geometric:= false)

vprintf G3Twists, 2 : "\n[G3Twists] D2 : JI = %o\n", JI;

    J2, J3, J4, J5, J6, J7, J8, J9, J10, J12:= Explode(JI);
    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    /* Special singular case only J9 <> 0 */
    if J2 eq 0 and J3 eq 0 and J4 eq 0 and J5 eq 0 and J6 eq 0 and J7 eq 0 and J8 eq 0 and J10 eq 0 and J12 eq 0 then
	f:= x^3*(x-1)^3*(x+1)^2;
	vprintf G3Twists, 2 : "[G3Twists] D2 : *** f = %o\n", f;
	if geometric then return [f]; end if;
	return "[G3Twists] currently, no twists computation done in singular case";
    end if;

    /* Special singular case [ 0, 1, 0, 0, 1, 0, 0, J9, 0, 2 ] */
    if J2 eq 0 and J4 eq 0 and J5 eq 0 and J7 eq 0 and J8 eq 0 and J10 eq 0 and
       J6 + 2*J3^2 eq 0 and J12 + J3^4 eq 0 then

	Pa:= x^3 + J9/J3^3;

	if not IsIrreducible(Pa) then
	    a:= [r[1] : r in Roots(Pa)][1];
	else
	    if not IsFinite(FF) then
		K3:= quo<Parent(x) | Pa>;
		a:= K3.1; x:= PolynomialRing(K3).1;
	    else
		K3:= ExtensionField<FF, x | Pa>;
		a:= K3.1; x:= PolynomialRing(K3).1;
	    end if;
	end if;

	f:= a*x^8 + x^6 + x^4 + x^2;

	vprintf G3Twists, 2 : "[G3Twists] D2 : *** f = %o\n", f;
	if geometric then return [f]; end if;
	return "[G3Twists] currently, no twists computation done in singular case";
    end if;

    /* I1 (= a4) */
    if J2^5*J4 + J3^2*J4^2 + 2*J2*J4^3 + 2*J3^3*J5 + 2*J2*J3*J4*J5 + J2^2*J5^2 + J4*J5^2 + J2*J3^2*J6 + 2*J4^2*J6
       + J3*J5*J6 + J3*J4*J7 + J7^2 + J3^2*J8 + 2*J2*J4*J8 + 2*J6*J8 + J2^2*J10 + J4*J10 + J2*J12 ne 0 then
	I1:= 2 * (2*J2^3*J3^3 + J2^4*J3*J4 + J2*J3^3*J4 + 2*J2^5*J5 + J2^2*J3^2*J5 + J3^2*J4*J5 + 2*J2*J4^2*J5 +
		  2*J2*J3*J5^2 + 2*J5^3 + 2*J2^3*J3*J6 + 2*J2*J3*J4*J6 + J2*J3^2*J7 + J2^2*J4*J7 + 2*J3*J5*J7 +
		  2*J2^2*J3*J8 + J3*J4*J8 + J2*J5*J8 + 2*J2*J4*J9 + J2*J3*J10 + 2*J5*J10)
	     /(J2^5*J4 + J3^2*J4^2 + 2*J2*J4^3 + 2*J3^3*J5 + 2*J2*J3*J4*J5 + J2^2*J5^2 + J4*J5^2 + J2*J3^2*J6 + 2*J4^2*J6
	       + J3*J5*J6 + J3*J4*J7 + J7^2 + J3^2*J8 + 2*J2*J4*J8 + 2*J6*J8 + J2^2*J10 + J4*J10 + J2*J12);
    elif J2^4*J3^2 + J3^2*J4^2 + J2^2*J5^2 + 2*J4*J5^2 + 2*J2^4*J6 + 2*J2*J3^2*J6 + 2*J4^2*J6 + J3*J4*J7 +
    2*J2*J5*J7 + 2*J7^2 + J3^2*J8 + J2*J4*J8 + 2*J6*J8 + 2*J2^2*J10 + J4*J10 + 2*J2*J12 ne 0 then
	I1:= 2 * (2*J3^5 + J2^4*J3*J4 + J2*J3^3*J4 + J2^5*J5 + J2^2*J3^2*J5 + 2*J2^3*J4*J5 + J3^2*J4*J5 + J2*J4^2*J5 +
		  2*J2^3*J3*J6 + 2*J3^3*J6 + 2*J2*J3*J4*J6 + 2*J2^2*J5*J6 + J4*J5*J6 + 2*J3*J6^2 + J2^4*J7 +
		  2*J2*J3^2*J7 + J3*J5*J7 + J2^2*J3*J8 + 2*J3*J4*J8 + 2*J2*J5*J8 + J7*J8 + 2*J2^3*J9 + J2*J4*J9 + 2*J5*J10)
	     /(J2^4*J3^2 + J3^2*J4^2 + J2^2*J5^2 + 2*J4*J5^2 + 2*J2^4*J6 + 2*J2*J3^2*J6 + 2*J4^2*J6 + J3*J4*J7 +
	       2*J2*J5*J7 + 2*J7^2 + J3^2*J8 + J2*J4*J8 + 2*J6*J8 + 2*J2^2*J10 + J4*J10 + 2*J2*J12);
    elif J2*J3^4 + J2^3*J4^2 + 2*J3^2*J4^2 + 2*J2*J3*J4*J5 + J2^2*J5^2 + J2*J3^2*J6 + J4^2*J6 + J3*J4*J7 + J2*J5*J7 +
    J7^2 + 2*J3^2*J8 + J2*J4*J8 + J6*J8 + 2*J2^2*J10 + J4*J10 + 2*J2*J12 ne 0 then
	I1:= 2 * (J2^3*J3^3 + J3^5 + J2^4*J3*J4 + 2*J2^2*J3*J4^2 + J2^5*J5 + J2^2*J3^2*J5 + J5^3 + J2^3*J3*J6 + J3^3*J6 +
		  2*J2^2*J5*J6 + J3*J6^2 + 2*J2*J3^2*J7 + 2*J2^2*J4*J7 + J2*J6*J7 + J2^2*J3*J8 + 2*J2*J5*J8 + J2*J4*J9 + 2*J2*J3*J10 + J5*J10)
	     /(J2*J3^4 + J2^3*J4^2 + 2*J3^2*J4^2 + 2*J2*J3*J4*J5 + J2^2*J5^2 + J2*J3^2*J6 + J4^2*J6 + J3*J4*J7 + J2*J5*J7 +
	       J7^2 + 2*J3^2*J8 + J2*J4*J8 + J6*J8 + 2*J2^2*J10 + J4*J10 + 2*J2*J12);
    else /* special singular case J3 = 0 and Ji <> 0, for i <> 3 */
	I1:= 0;
    end if;

    /* I2a (= a0*a8) */
    if I1 ne 0 then
	I2a:= 2 * (I1^4 + I1^2*J2 + 2*I1*J3)/I1^2;
    elif J2^3 + 2*J6 ne 0 then
	I2a:= 2 * ( 2*J2^4 + J2^2*J4 + J4^2 + 2*J2*J6 ) / (J2^3 + 2*J6);
    else I2a:= 2*J2; // singular case a8*a0 + 2*a6*a2 = 0, a4 = 0 => J2 = 2*a8*a0 et J3 = 0
    end if;

    /* I2b (= a2*a6) */
    I2b:= J2 + 2*I2a + I1^2;

    /* I3 (= a0*a6^2 + a2^2*a8) */
    if I2a ne 0 then
	I3:=  2 * (I1*I2b*J2^2 + 2*I2a^2*J3 + I2b^2*J3 + J2^2*J3 + 2*I1*I2b*J4 + I1*J2*J4 + J3*J4 + 2*I2a*J5 +
		   2*I2b*J5 + 2*J2*J5 + 2*I1*J6 + 2*J7) / I2a^2;
    elif J2 ne 0 then
	I3:= (2*J5 + 2*I1*I2b^2 + I1^5)/J2;

	A0:= 0;
	A2:= 1;
	A4:= I1;
	A6:= I2b;
	A8:= I3;

	f:= A8*x^8 + A6*x^6 + A4*x^4 + A2*x^2 + A0;

	vprintf G3Twists, 2 : "[G3Twists] D2 : *** f = %o\n", f;
	if geometric then return [f]; end if;
	return "[G3Twists] currently, no twists computation done in singular case";
    else
	error "[G3Twists] special singular case [ 0, 1, 0, 0, 1, 0, 0, J9, 0, 2 ]";
    end if;

    vprintf G3Twists, 2 : "[G3Twists] D2 : *** I1 = %o, I2a = %o, I2b = %o, I3f = %o\n", I1, I2a, I2b, I3;

    /* Some easy cases */
    if I2b eq 0 then
	A2:= 0;
	A6:= 1;
	A4:= I1;
	A0:= I3;
	A8:= I2a/I3;

	f:= A8*x^8 + A6*x^6 + A4*x^4 + A2*x^2 + A0;

	vprintf G3Twists, 2 : "[G3Twists] D2 : *** f = %o\n", f;
	if geometric then return [f]; end if;
	return HyperellipticPolynomialTwists(f, 8);
    end if;

    d:= (I3^2 + 2*I2a*I2b^2);

    /* Can we realize this curve with a normal model ? */
    normalmodel, t:= IsSquare(d);

    if not normalmodel then
	P3:= PolynomialRing(FF, 3); A:= P3.1; B:= P3.2; C:= P3.3;
	Cn:= A^2 - d*B^2 -I2b*C^2;
	a, b:= FindPointOnConic(Cn);
	if not a in FF or not b in FF then
	    K2:= ExtensionField<FF, x| x^2 - d>; t:= K2.1;
	    x:= PolynomialRing(K2).1;
	    normalmodel:= true;
	end if;
    end if;

    if normalmodel then

	A2:= 1;
	A0:= 2/I2b^2*(I3+t);
	A4:= I1;
	A6:= I2b/A2;
	A8:= I2a/A0;

	f:= A8*x^8 + A6*x^6 + A4*x^4 + A2*x^2 + A0;

	vprintf G3Twists, 2 : "[G3Twists] D2 : *** f = %o\n", f;
	if geometric then return [f]; end if;
	return HyperellipticPolynomialTwists(f, 8);

    end if;

    /* Can we realize this curve with a twisted normal model ? */
    X:= PolynomialRing(Parent(a)).1;

    Pt:= X^2-d;
    Ft:= Sort(Factorization(Pt), func<x, y| Degree(x[1]) - Degree(y[1])>);

    Pt:= Ft[1, 1]; Pt /:= Coefficient(Pt, Degree(Pt));
    if Degree(Pt) eq 2 then
	K2:= ExtensionField<FF, x | Pt>; t:= K2.1;
    else
	K2:= FF;  t:= - Coefficient(Pt, 0);
    end if;
    X:= PolynomialRing(K2).1;

    A2:= a + b*t;
    A0:= (1/2/I2b^2*(I3+t))*A2^2; // A0:= (1/2/I2a^2*(I3-t))*A2^2;
    A4:= I1;
    A6:= I2b/A2;
    A8:= I2a/A0;

    a0:= A0+A4+A6+A8+A2;
    a1:= -4*t*(-2*A0+A6+2*A8-A2);
    a2:= 28*(t^2)*A0-4*A4*(t^2)+4*(t^2)*A6+28*(t^2)*A8+4*(t^2)*A2;
    a3:= 56*t^3*A0+4*t^3*A6-56*t^3*A8-4*t^3*A2;
    a4:= 6*A4*(t^2)^2+70*(t^2)^2*A0-10*(t^2)^2*A6+70*(t^2)^2*A8-10*(t^2)^2*A2;

    K, phi:= sub<Parent(t) | a0, a1, a2, a3, a4>;
    X:= PolynomialRing(K).1; d:= K!phi(t^2);
    f:=
       K!phi(a0)*X^8+K!phi(a1)*X^7+K!phi(a2)*X^6+K!phi(a3)*X^5+K!phi(a4)*X^4+
       d*K!phi(a3)*X^3+d^2*K!phi(a2)*X^2+d^3*K!phi(a1)*X+d^4*K!phi(a0);

    vprintf G3Twists, 2 : "[G3Twists] D2 : *** f = %o\n", f;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;
