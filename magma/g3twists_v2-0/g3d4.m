//freeze;

/***
 *  Reconstruction of genus 3 hyperelliptic curves with automorphism group
 *  equal to D4
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

import "conic.m"       : FindPointOnConic;

/* Case D4

   y^2 = a8 * x^8 + a6 * x^6 + a4 * x^4 + a2 * x^2 + a0;
*/
function G3ModelsInCharFF_D4(JI : geometric := false, RationalModel := true)

    vprintf G3Twists, 2 : "\n[G3Twists] D4: JI = %o\n", JI;

    J2, J3, J4, J5, J6, J7, J8, J9, J10 := Explode(JI);
    FF := Universe(JI); x := PolynomialRing(FF).1;

    /* I1 */
    den :=
	366660*J4*J3^2*J2-1377810*J5*J4*J3+4039470*J6*J4*J2+88200*J3^4+98*J2^6+551124*J4^3+6917400*J6^2-4592700*J9*J3+4592700*J10*J2-5880*J3^2*J2^3-12222*J4*J2^4+351540*J4^2*J2^2-41895*J6*J2^3+1256850*J6*J3^2-535815*J5^2*J2-8037225*J7*J5;
    if den ne 0 then
	I1 := 945/8*(252*J4*J3*J2^3-11340*J4^2*J3*J2-5880*J5*J3^2*J2-5418*J5*J4*J2^2+196*J5*J2^4-7560*J4*J3^3-4620*J7*J2^3-269244*J5*J4^2+79380*J5^2*J3+138600*J7*J3^2+11340*J9*J2^2+434700*J7*J6-1275750*J8*J5+1224720*J9*J4-340200*J10*J3-159570*J6*J4*J3-41895*J6*J5*J2+207900*J7*J4*J2)/den;
    else
	I1 := 945/8*(56*J4*J3*J2^3-2520*J4^2*J3*J2-840*J5*J3^2*J2-504*J5*J4*J2^2+28*J5*J2^4-1680*J4*J3^3-840*J7*J2^3-59292*J5*J4^2+11340*J5^2*J3+25200*J7*J3^2+94500*J7*J6-255150*J8*J5+272160*J9*J4-23310*J6*J4*J3-11655*J6*J5*J2+43470*J7*J4*J2)/(60480*J4*J3^2*J2-306180*J5*J4*J3+839160*J6*J4*J2+12600*J3^4+14*J2^6+78732*J4^3+1134000*J6^2-840*J3^2*J2^3-2016*J4*J2^4+62370*J4^2*J2^2-11655*J6*J2^3+349650*J6*J3^2-76545*J5^2*J2-1148175*J7*J5-2296350*J8*J4);
    end if;

    /* I2a */
    den := 192*I1^3-8575*J3-1470*I1*J2;
    if den ne 0 then
	I2a := -2/125*(1152*I1^5-18907875*J5-7203000*I1*J4+771750*I1^2*J3-102900*I1^3*J2+6302625*J3*J2+1200500*I1*J2^2)/den;
    else
	I2a := -2/3375*(718848*I1^6+264710250000*J6-57177414000*I1*J5-1037232000*I1^2*J4+666792000*I1^3*J3-67737600*I1^4*J2+46324293750*J4*J2+2042050500*I1*J3*J2+740108250*I1^2*J2^2-367653125*J2^3)/(274400*I1*J3+3072*I1^4-5762400*J4+60025*J2^2);
    end if;

    /* I2b */
    I2b := -1/28*I2a-1/140*I1^2+1/2*J2;

    /* I3 */
    I3  := 5/21*I2a*I1+8/525*I1^3+392/9*J3-28/15*I1*J2;

    vprintf G3Twists, 2 : "[G3Twists] D4: *** I1 = %o, I2a = %o, I2b = %o, I3f = %o\n", I1, I2a, I2b, I3;

    /* Some easy cases */
    if I2a eq 0 then
	A2 := 0;
	A6 := 1;
	A4 := I1;
	A0 := I3;
	A8 := I2b/I3;

	f := A8*x^8 + A6*x^6 + A4*x^4 + A2*x^2 + A0;

	vprintf G3Twists, 2 : "[G3Twists] D4: *** f = %o\n", f;
	if geometric then return [f]; end if;
	return HyperellipticPolynomialTwists(f, 8);
    end if;

    /* Some easy cases */
    if I2b eq 0 then
	A0 := 0;
	A2 := 1;
	A4 := I1;
	A6 := I2a;
	A8 := I3;

	f := A8*x^8 + A6*x^6 + A4*x^4 + A2*x^2 + A0;

	vprintf G3Twists, 2 : "[G3Twists] D4: *** f = %o\n", f;
	if geometric then return [f]; end if;
	return HyperellipticPolynomialTwists(f, 8);

    end if;

    d := (-4*I2a^2*I2b+I3^2);

    /* Can we realize this curve with a normal model */
    normalmodel, t := IsSquare(d);
    if not normalmodel then
	P2 := ProjectiveSpace(FF, 2); A := P2.1; B := P2.2; C := P2.3;
	Cn := 4*I2a^2*I2b*B^2-I2a*C^2-I3^2*B^2+A^2;

	HasRatPoint, Pt := HasRationalPoint(Conic(P2, Cn));
	if not HasRatPoint then
	    K2 := ExtensionField<FF, x| x^2 - d>; t := K2.1;
	    x := PolynomialRing(K2).1;
	    normalmodel := true;
	else
	    a,b,_ := Explode(Eltseq(Pt));
	end if;

    end if;

    if normalmodel then

	A2 := 1;
	A0 := (1/2/I2a^2*(I3+t))*A2^2; // A0 := (1/2/I2a^2*(I3-t))*A2^2;
	A4 := I1;
	A6 := I2a/A2;
	A8 := I2b/A0;

	f := A8*x^8 + A6*x^6 + A4*x^4 + A2*x^2 + A0;

	vprintf G3Twists, 2 : "[G3Twists] D4: *** f = %o\n", f;
	if geometric then return [f]; end if;
	return HyperellipticPolynomialTwists(f, 8);

    end if;

    /* Can we realize this curve with a twisted normal model ? */
    Pt := x^2-(-4*I2a^2*I2b+I3^2);
    Ft := Sort(Factorization(Pt), func<x, y| Degree(x[1]) - Degree(y[1])>);

    Pt := Ft[1, 1]; Pt /:= Coefficient(Pt, Degree(Pt));
    if Degree(Pt) eq 2 then
	K2 := ExtensionField<FF, x | Pt>; t := K2.1;
    else
	K2 := FF;  t := - Coefficient(Pt, 0);
    end if;
    X := PolynomialRing(K2).1;

    A2 := a + b*t;
    A0 := (1/2/I2a^2*(I3+t))*A2^2; // A0 := (1/2/I2a^2*(I3-t))*A2^2;
    A4 := I1;
    A6 := I2a/A2;
    A8 := I2b/A0;

    a0 := A0+A4+A6+A8+A2;
    a1 := -4*t*(-2*A0+A6+2*A8-A2);
    a2 := 28*(t^2)*A0-4*A4*(t^2)+4*(t^2)*A6+28*(t^2)*A8+4*(t^2)*A2;
    a3 := 56*t^3*A0+4*t^3*A6-56*t^3*A8-4*t^3*A2;
    a4 := 6*A4*(t^2)^2+70*(t^2)^2*A0-10*(t^2)^2*A6+70*(t^2)^2*A8-10*(t^2)^2*A2;

    K, phi := sub<Parent(t) | a0, a1, a2, a3, a4>;
    X := PolynomialRing(K).1; d := K!phi(t^2);
    f :=
	K!phi(a0)*X^8+K!phi(a1)*X^7+K!phi(a2)*X^6+K!phi(a3)*X^5+K!phi(a4)*X^4+
	d*K!phi(a3)*X^3+d^2*K!phi(a2)*X^2+d^3*K!phi(a1)*X+d^4*K!phi(a0);

    vprintf G3Twists, 2 : "[G3Twists] D4: *** f = %o\n", f;
    if geometric then return [f]; end if;
    return HyperellipticPolynomialTwists(f, 8);

end function;
