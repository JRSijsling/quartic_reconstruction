//freeze;

/***
 *  Rings of characteristic 2
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
 *  Copyright 2011-2012, R. Basson & R. Lercier & C. Ritzenthaler
 */

import "sl2invtools.m"    : PowerRepresentativesInFiniteFields, ShiodaInvariantsAppend;

function Genus3WeierstrassToArtinSchreierModel_T1111(f, h)

    Px := Parent(f); x := Px.1;

    f0 := Coefficient(f, 0); f1 := Coefficient(f, 1);
    f2 := Coefficient(f, 2); f3 := Coefficient(f, 3);
    f4 := Coefficient(f, 4); f5 := Coefficient(f, 5);
    f6 := Coefficient(f, 6); f7 := Coefficient(f, 7);
    f8 := Coefficient(f, 8);

    h0 := Coefficient(h, 0); h1 := Coefficient(h, 1);
    h2 := Coefficient(h, 2); h3 := Coefficient(h, 3);
    h4 := Coefficient(h, 4);

    J3 := h3^2*h0+h3*h2*h1+h4*h1^2;

    if h0 ne 0 then
	if h1 ne 0 then
	    /* J3 <> 0, otherwise we have a Type (1,1,3) curve  */

	    T0 :=
		0;
	    T1 :=
		1/h0^2*(h4*h1^2*f2*h0^2+h4*h1^3*f1*h0+h4*h1^4*f0+h4*h1*f3*h0^3+h3^2*f1*h0^2*h1+h3*h2*h1^2*f1*h0+h3*h2*h1^3*f0+h4*h2*f1*h0^2*h1+h3*h2*f2*h0^2*h1+h3^2*h1^2*f0*h0+h3*h2^2*f1*h0^2+h3*h2*f3*h0^3+h4*h3*f1*h0^3+h0^4*f7*h1+h3^2*f2*h0^3+h3*h0^4*f5)/J3;
	    T2 :=
		1/h0^2*(h0^3*f5*h4*h1+h4^2*f1*h0^2*h1+h3^3*h0^2*f1+h3*h0^4*f7+h1^3*h0^2*f7+h2^2*f0*h0*h3^2+h1*h2^3*f0*h3+h1^2*h2^2*f0*h4+h0^3*f5*h3*h2+h2^2*f1*h0*h4*h1+h2^2*f3*h0^2*h3+h2*f3*h0^2*h4*h1+h2^3*f1*h0*h3+h1*f4*h0^2*h3*h2+h3*h0^3*h4*f3+h1^2*h3*h0^2*f5+h1*f3*h0^2*h3^2+f4*h0^3*h3^2+h1^2*f4*h0^2*h4)/J3;
	    T3 :=
		1/h0^2*(h2*h3^3*h1*f0+h2*h0^2*f5*h4*h1+h2*h3^3*h0*f1+h2*h3*h0^3*f7+h3*h1^2*h0^2*f7+h3^2*h1*h0^2*f5+h2^2*h0^2*h1*f7+h4^2*h0^2*h1*f3+h4*h0^3*h1*f7+h0^3*f6*h3^2+h0^2*f6*h1^2*h4+h3^3*f3*h0^2+h3^4*f0*h0+h4*h1^2*h3^2*f0+h4^2*h0^2*h3*f1+h4*h0^3*h3*f5+h0^2*f6*h1*h3*h2+h3^2*h1*h0*h4*f1)/J3;
	    T4 :=
		1/h0^2*(h3*h0^2*h4^2*f3+h4*h3*h0^3*f7+h0^2*f8*h1*h3*h2+h4^3*f0*h1^2+h0^3*f8*h3^2+h0^2*f8*h1^2*h4+h0^2*f5*h4^2*h1+h4^3*f1*h0*h1+h4^2*f0*h0*h3^2+h4^2*f0*h1*h3*h2+h4^2*h2*h0*h3*f1+h4*h2*h0^2*h1*f7)/J3;

	    T := Px![Sqrt(t) : t in [T0, T1, T2, T3, T4]];

	    F := f + T*h + T^2; Fp := F div h;
	    abcd := [Coefficient(Fp, i) : i in [0..4]] cat
		[Coefficient(h, i) : i in [0..4]];
	    return F, h, abcd;

	end if;

	/* h1 = 0, and thus h3 <> 0 , otherwise we have a Type (3, 3) curve  */
	if h2 ne 0 then
	    T2 :=
		0;
	    T0 :=
		(h3*f4*h0^2+h0^3*f7+h4*f3*h0^2+h3^2*f1*h0+h2^3*f1+h2^2*f3*h0+h2*h0^2*f5+h3*h2^2*f0)/h3/h2^2;
	    T1 :=
		1/h0*(h2^2*f1+h2*f3*h0+h0^2*f5+h3*f2*h0+h4*f1*h0)/h3;
	    T3 :=
		1/h0*(h3^3*h0*T2+h3^3*h0*f4+h3^2*h0^2*f7+h3^4*f1+h2^3*h0*f7+h0*f6*h3*h2^2+h4*h0*h2^2*f5+h4^2*h2^2*f1+h3^2*h0*h4*f3+h3^2*h0*h2*f5+h2^3*h3*T2)/h2^2/h3;
	    T4 :=
		1/h0*(h4*h2^2*h3*T2+h0*f8*h3*h2^2+h4*h2^2*h0*f7+h4^2*h0*h3*T2+h4^2*h0*h3*f4+h4^2*h3^2*f1+h4^2*h0*h2*f5+h4^2*h0^2*f7+h4^3*h0*f3)/h2^2/h3;

	    T := Px![Sqrt(t) : t in [T0, T1, T2, T3, T4]];

	    F := f + T*h + T^2; Fp := F div h;
	    abcd := [Coefficient(Fp, i) : i in [0..4]] cat
		[Coefficient(h, i) : i in [0..4]];
	    return F, h, abcd;

	end if;

	/* h2 = 0 */
	T0 := 0;
	T2 := (h4*f3*h0+h3^2*f1+h3*f4*h0+h0^2*f7)/h3/h0;
	T1 := (h3*f2+h0*f5+h4*f1)/h3;
	T3 := 1/h0^2*(h4*h0^2*f5+h4^2*h0*f1+h3^2*f3*h0+h3^3*f0+h0^2*f6*h3)/h3;
	T4 := 1/h0^2*(h0^2*f8*h3+h4^2*f0*h3+h4^2*f3*h0+h4*h0^2*f7)/h3;

	T := Px![Sqrt(t) : t in [T0, T1, T2, T3, T4]];

	F := f + T*h + T^2; Fp := F div h;
	abcd := [Coefficient(Fp, i) : i in [0..4]] cat
	    [Coefficient(h, i) : i in [0..4]];
	return F, h, abcd;


    end if;

    /* h0 = 0, but h1 <> 0, otherwise we have a Type (1,1,3) curve  */
    /* and J3 <> 0 implies h4*h1+h3*h2 <> 0 */
    T0 :=
	f0;
    T1 :=
	0;
    T2 :=
	(h1^5*f7+h3^2*h2^2*f1*h1+h3^2*f3*h1^3+h3^3*f1*h1^2+h3*h1^4*f5+h3*h2*f4*h1^3+h3*h2^4*f1+h3*h2^3*f2*h1+h3*h2^2*f3*h1^2+h4*f4*h1^4+h4^2*f1*h1^3+h4*h2^3*f1*h1+h4*h2^2*f2*h1^2+h4*h2*f3*h1^3)/h1^3/(h4*h1+h3*h2);
    T3 :=
	1/h1^3*(h3*h1^2*h4^2*f1+h2*h1^3*f5*h4+h1^3*f6*h3*h2+h2*h3^2*f1*h1*h4+h3*h1^4*f7+h3^3*h1^2*f3+h3^4*h1*f1+h3^2*h1^3*f5+h4^2*f3*h1^3+h2^2*h1^3*f7+h1^4*f6*h4+h3^2*f2*h1^2*h4+h3^3*f2*h1*h2+h3^3*h2^2*f1)/(h4*h1+h3*h2);
    T4 :=
	1/h1^3*(h4^2*f2*h1*h3*h2+h4^3*h2*f1*h1+h1^3*f8*h3*h2+h4^2*h1^3*f5+h4^3*f2*h1^2+h1^4*f8*h4+h4^2*h3*f3*h1^2+h4^2*h3^2*f1*h1+h4*h2*h1^3*f7+h4^2*h3*h2^2*f1)/(h4*h1+h3*h2);

    T := Px![Sqrt(t) : t in [T0, T1, T2, T3, T4]];

    F := f + T*h + T^2; Fp := F div h;
    abcd := [Coefficient(Fp, i) : i in [0..4]] cat
	[Coefficient(h, i) : i in [0..4]];
    return F, h, abcd;

end function;

function Genus3WeierstrassToArtinSchreierModel_T113(f, h)

    Px := Parent(f); x := Px.1;

    /* First, let us obtain an equivalent curve Y^2 + Y = F/H^2 with H of degree 2 */
    f0 := Coefficient(f, 0); f1 := Coefficient(f, 1);
    f2 := Coefficient(f, 2); f3 := Coefficient(f, 3);
    f4 := Coefficient(f, 4); f5 := Coefficient(f, 5);
    f6 := Coefficient(f, 6); f7 := Coefficient(f, 7);
    f8 := Coefficient(f, 8);

    h0 := Coefficient(h, 0); h1 := Coefficient(h, 1);
    h2 := Coefficient(h, 2); h3 := Coefficient(h, 3);
    h4 := Coefficient(h, 4);

    if h1 ne 0 then
	if h3 ne 0 then
	    h0 := Sqrt(h0); h1 := Sqrt(h1); h2 := Sqrt(h2);
	    h3 := Sqrt(h3); h4 := Sqrt(h4);

	    F := h1^8 * (
		(f0*h3^8+f8*h1^8+f7*h3*h1^7+f6*h3^2*h1^6+f5*h3^3*h1^5+f4*h3^4*h1^4+f3*h3^5*h1^3+f2*h3^6*h1^2+f1*h3^7*h1)*x^8+
		(f7*h3*h1^6+f5*h3^3*h1^4+f3*h3^5*h1^2+f1*h3^7)*x^7+
		(f2*h3^6+f7*h3*h1^5+f3*h3^5*h1+f6*h3^2*h1^4)*x^6+
		(f7*h3*h1^4+f3*h3^5)*x^5+
		(f5*h3^3*h1+f7*h3*h1^3+f4*h3^4+f6*h3^2*h1^2)*x^4+
		(f7*h3*h1^2+f5*h3^3)*x^3+
		(f6*h3^2+f7*h3*h1)*x^2+
		f7*h3*x+
		f8
		)/h3^4;
	    H :=
		(h1^5*h3+h2^2*h1^4)*x^2+
		h1^4*h3*x+
		h2^2*h1^2+h0^2*h3^2;
	else
	    F := f;
	    H := h;		/* J3 = 0 => h4 = 0 */
	end if;
    else
	/* h1 = 0 and thus h0 = 0 otherwise h3 = 0, and we have a Type (3,3) curve */

	F := f8 + f7*x + f6*x^2 + f5*x^3 + f4*x^4 + f3*x^5 + f2*x^6 + f1*x^7 + f0*x^8;
	H := h2*x^2 + h3*x + h4;
    end if;

    n0 := Sqrt(Coefficient(F, 0)); n1 := Sqrt(Coefficient(F, 1));
    n2 := Sqrt(Coefficient(F, 2)); n3 := Sqrt(Coefficient(F, 3));
    n4 := Sqrt(Coefficient(F, 4)); n5 := Sqrt(Coefficient(F, 5));
    n6 := Sqrt(Coefficient(F, 6)); n7 := Sqrt(Coefficient(F, 7));
    n8 := Sqrt(Coefficient(F, 8));

    d0 := Sqrt(Coefficient(H, 0));  d1 := Sqrt(Coefficient(H, 1));
    d2 := Sqrt(Coefficient(H, 2));  d3 := Sqrt(Coefficient(H, 3));
    d4 := Sqrt(Coefficient(H, 4));

    if d0 ne 0 then

	/* d1 <> 0, otherwise we have a Type (3,3) curve */
	a :=
	    (n7/d2^5*d1^3)^2;
	b :=
	    1/d2^20*(n7^4*d1^8+d2^8*n8^2*d1^4+d2^12*n6^2+d2^8*n5^4+n8*d2^14)*d1^4;
	e :=
	    1/d2^16*(n7^2*d2^6*d1^12+d2^10*n8*d1^10+d0^4*n7^4*d1^10+n7*d2^11*d1^9+d2^10*n5^2*d1^8+d2^12*n6*d1^8+n5*d2^13*d1^7+d2^12*d0*n7*d1^7+d2^14*n4*d1^6+d2^8*d0^4*n8^2*d1^6+d2^15*n3*d1^5+d2^14*d0*n5*d1^5+d2^16*n2*d1^4+d2^14*d0^2*n6*d1^4+d2^14*n3^2*d1^4+d2^15*d0^2*n5*d1^3+d2^16*d0*n3*d1^3+d2^14*d0^3*n7*d1^3+n1*d2^17*d1^3+d2^8*d0^4*n5^4*d1^2+d2^12*n6^2*d0^4*d1^2+d2^16*n2^2*d1^2+d2^16*n3^2*d0^2+n1^2*d2^18+d2^12*n7^2*d0^6+d2^14*n5^2*d0^4)/d1^6;
	c :=
	    (d2^8*d0*n5*d1^5+n5*d2^7*d1^7+d2^4*n5^2*d1^8+d2^6*n6*d1^8+d2^9*n3*d1^5+d2^10*d0*n3*d1^3+n1*d2^11*d1^3+n7^2*d1^12+d2^4*n8*d1^10+n7*d2^5*d1^9+d0^4*d2^4*n7^2*d1^4+d2^8*n3^2*d1^4+d2^8*d0^2*n6*d1^4+d2^10*n2*d1^4+d2^6*d0*n7*d1^7+d2^8*n4*d1^6+d2^8*d0^3*n7*d1^3+d2^9*d0^2*n5*d1^3)/d2^10/d1^6;
	d :=
	    (d2^8*d0^2*n6*d1^4+d2^6*d0^2*n5^2*d1^4+d0^4*d2^4*n7^2*d1^4+d2^2*d0^2*n7^2*d1^8+d2^12*d0*n1*d1+d0^3*d2^10*n5*d1+d0^2*d2^11*n3*d1+d2^9*d0^2*n5*d1^3+d2^8*d0^3*n7*d1^3+d0^2*d2^6*n8*d1^6+d2^10*d0^2*n3^2+d0^4*d2^8*n8*d1^2+d0^2*d2^7*n7*d1^5+d2^12*n0*d1^2+d0^2*d2^10*n4*d1^2+d0^4*d2^9*n7*d1+d2^6*d0^6*n7^2+d2^8*d0^4*n5^2+d2^12*n1^2)/d2^10/d1^6;
	s :=
	    (1/d1^2*d0*d2)^2;

	return
	    ((a*x^3+b*x^2+e)*(x^2+x+s)+c*x+d)*(x^2+x+s),
	    (x^2+x+s),
	    [a, b, c, d, e, s];

    end if;

    /* d0 = 0, but d1 <> 0, d2 <> 0, otherwise we have a Type (3,3) or (1,5) curve */
    a :=
	(n7*d1^3/d2^5)^2;
    b :=
	1/d2^20*(n7^4*d1^8+d2^8*n8^2*d1^4+n6^2*d2^12+d2^8*n5^4+n8*d2^14)*d1^4;
    e :=
	(n7^2*d1^12+d2^4*n8*d1^10+n7*d2^5*d1^9+d2^4*n5^2*d1^8+d2^6*n6*d1^8+n5*d2^7*d1^7+d2^8*n4*d1^6+n3*d2^9*d1^5+d2^8*n3^2*d1^4+d2^10*n2*d1^4+n1*d2^11*d1^3+d2^10*n2^2*d1^2+d2^12*n1^2)/d2^10/d1^6;
    c :=
	(n7^2*d1^12+d2^4*n8*d1^10+n7*d2^5*d1^9+d2^6*n6*d1^8+d2^4*n5^2*d1^8+n5*d2^7*d1^7+d2^8*n4*d1^6+n3*d2^9*d1^5+d2^8*n3^2*d1^4+d2^10*n2*d1^4+n1*d2^11*d1^3)/d1^6/d2^10;
    d :=
	(d2^12*n0*d1^2+d2^12*n1^2)/d1^6/d2^10;
    s :=
	0*n0;

    return
	((a*x^3+b*x^2+e)*(x^2+x+s)+c*x+d)*(x^2+x+s),
	(x^2+x+s),
	[a, b, c, d, e, s];

end function;

function Genus3WeierstrassToArtinSchreierModel_T33(f, h)

    Px := Parent(f); x := Px.1;

    f0 := Sqrt(Coefficient(f, 0)); f1 := Sqrt(Coefficient(f, 1));
    f2 := Sqrt(Coefficient(f, 2)); f3 := Sqrt(Coefficient(f, 3));
    f4 := Sqrt(Coefficient(f, 4)); f5 := Sqrt(Coefficient(f, 5));
    f6 := Sqrt(Coefficient(f, 6)); f7 := Sqrt(Coefficient(f, 7));
    f8 := Sqrt(Coefficient(f, 8));

    h0 := Sqrt(Sqrt(Coefficient(h, 0)));  h1 := Sqrt(Sqrt(Coefficient(h, 1)));
    h2 := Sqrt(Sqrt(Coefficient(h, 2)));  h3 := Sqrt(Sqrt(Coefficient(h, 3)));
    h4 := Sqrt(Sqrt(Coefficient(h, 4)));

    if h4 ne 0 then
	/* h2 <> 0 otherwise, we have a Type (7) curve */
	e :=
	    ((f6*h2^2*h4^10+f8*h2^4*h4^8+f6^2*h4^8+f7^2*h2^2*h4^6+f7^4)/h2^4/h4^12)^2;
	c :=
	    ((h4^4*f3+f5*h2^2*h4^2+h0^2*f7*h4^2+f7*h2^4)/h2^5/h4^3)^2;
	d :=
	    ((h4^5*f1+h4^4*h0*f3+h0^2*f7*h2^2*h4+h4^3*h0^2*f5+h0*f5*h2^2*h4^2+h0^3*f7*h4^2+h0*f7*h2^4)/h2^7/h4^2)^2;
	a :=
	    ((h0^2*f6*h2*h4^12+h0*f5*h2^2*h4^12+f7*h0^3*h4^12+h4^14*f2*h2+f4*h2^3*h4^12+h0*f7*h2^4*h4^10+h4^13*h0^2*f5+h4^15*f1+f6^2*h2^3*h4^8+f8*h2^7*h4^8+f7*h2^6*h4^9+h4^14*h0*f3+f5*h2^4*h4^11+h4^13*f3*h2^2+h0^2*f7^2*h2*h4^8+f5^2*h2*h4^10+f7^4*h2^3+f6*h2^5*h4^10)/h2^7/h4^12);
	b :=
	    ((h4^28*h0*f1+h4^28*f0*h2+h0^2*f6*h2^3*h4^24+h4^27*h0^2*f3+h4^26*h0^2*f4*h2+h4^26*h0^3*f5+f7*h0^3*h2^2*h4^24+f8^2*h2^9*h4^16+h0^2*f7*h2^4*h4^23+h4^25*h0^2*f5*h2^2+f7^4*h2^5*h4^12+h4^25*h0^4*f7+f7^8*h2+f4^2*h2*h4^24+f8*h0^4*h2*h4^24+h0^2*f7^2*h2^3*h4^20+h0^2*f8*h2^5*h4^22+f6^4*h2*h4^16+h0^2*f6^2*h2*h4^22+f6^2*h2^5*h4^20+h0^2*f7^4*h2*h4^14)/h2^9/h4^24);
	s :=
	    (1/h2^2*h0*h4)^2;

	return
	    (e*(x^2+x+s)^3+(a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s),
	    (x^2+x+s)^2,
	    [a, b, c, d, e, s];

    end if;

    /* h4 eq 0, but h0 <> 0, apply x -> 1/x to be in the previous case */
    if h0 ne 0 then

	e :=
	    ((f2*h2^2*h0^10+f0*h2^4*h0^8+f2^2*h0^8+f1^2*h2^2*h0^6+f1^4)/h2^4/h0^12)^2;
	c :=
	    ((h0^4*f5+f3*h2^2*h0^2+h4^2*f1*h0^2+f1*h2^4)/h2^5/h0^3)^2;
	d :=
	    ((h0^5*f7+h0^4*h4*f5+h4^2*f1*h2^2*h0+h0^3*h4^2*f3+h4*f3*h2^2*h0^2+h4^3*f1*h0^2+h4*f1*h2^4)/h2^7/h0^2)^2;
	a :=
	    ((h4^2*f2*h2*h0^12+h4*f3*h2^2*h0^12+f1*h4^3*h0^12+h0^14*f6*h2+f4*h2^3*h0^12+h4*f1*h2^4*h0^10+h0^13*h4^2*f3+h0^15*f7+f2^2*h2^3*h0^8+f0*h2^7*h0^8+f1*h2^6*h0^9+h0^14*h4*f5+f3*h2^4*h0^11+h0^13*f5*h2^2+h4^2*f1^2*h2*h0^8+f3^2*h2*h0^10+f1^4*h2^3+f2*h2^5*h0^10)/h2^7/h0^12);
	b :=
	    ((h0^28*h4*f7+h0^28*f8*h2+h4^2*f2*h2^3*h0^24+h0^27*h4^2*f5+h0^26*h4^2*f4*h2+h0^26*h4^3*f3+f1*h4^3*h2^2*h0^24+f0^2*h2^9*h0^16+h4^2*f1*h2^4*h0^23+h0^25*h4^2*f3*h2^2+f1^4*h2^5*h0^12+h0^25*h4^4*f1+f1^8*h2+f4^2*h2*h0^24+f0*h4^4*h2*h0^24+h4^2*f1^2*h2^3*h0^20+h4^2*f0*h2^5*h0^22+f2^4*h2*h0^16+h4^2*f2^2*h2*h0^22+f2^2*h2^5*h0^20+h4^2*f1^4*h2*h0^14)/h2^9/h0^24);
	s :=
	    (1/h2^2*h4*h0)^2;

	return
	    (e*(x^2+x+s)^3+(a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s),
	    (x^2+x+s)^2,
	    [a, b, c, d, e, s];

    end if;

    /* h4 eq 0 and h0 eq 0, apply x -> 1/(x+1) to be in the previous case */
    g0 := (f8+f0+f7+f6+f5+f4+f3+f2+f1);
    g1 := (f7+f5+f3+f1); g2 := (f7+f2+f6+f3);
    g3 := (f7+f3);       g4 := (f5+f7+f6+f4);
    g5 := (f5+f7);       g6 := (f6+f7);
    g7 := f7;            g8 := f8;

    j0 := h2; j2 := h2; j4 := 0;

    e :=
	((g2*j2^2*j0^10+g0*j2^4*j0^8+g2^2*j0^8+g1^2*j2^2*j0^6+g1^4)/j2^4/j0^12)^2;
    c :=
	((j0^4*g5+g3*j2^2*j0^2+j4^2*g1*j0^2+g1*j2^4)/j2^5/j0^3)^2;
    d :=
	((j0^5*g7+j0^4*j4*g5+j4^2*g1*j2^2*j0+j0^3*j4^2*g3+j4*g3*j2^2*j0^2+j4^3*g1*j0^2+j4*g1*j2^4)/j2^7/j0^2)^2;
    a :=
	((j4^2*g2*j2*j0^12+j4*g3*j2^2*j0^12+g1*j4^3*j0^12+j0^14*g6*j2+g4*j2^3*j0^12+j4*g1*j2^4*j0^10+j0^13*j4^2*g3+j0^15*g7+g2^2*j2^3*j0^8+g0*j2^7*j0^8+g1*j2^6*j0^9+j0^14*j4*g5+g3*j2^4*j0^11+j0^13*g5*j2^2+j4^2*g1^2*j2*j0^8+g3^2*j2*j0^10+g1^4*j2^3+g2*j2^5*j0^10)/j2^7/j0^12);
    b :=
	((j0^28*j4*g7+j0^28*g8*j2+j4^2*g2*j2^3*j0^24+j0^27*j4^2*g5+j0^26*j4^2*g4*j2+j0^26*j4^3*g3+g1*j4^3*j2^2*j0^24+g0^2*j2^9*j0^16+j4^2*g1*j2^4*j0^23+j0^25*j4^2*g3*j2^2+g1^4*j2^5*j0^12+j0^25*j4^4*g1+g1^8*j2+g4^2*j2*j0^24+g0*j4^4*j2*j0^24+j4^2*g1^2*j2^3*j0^20+j4^2*g0*j2^5*j0^22+g2^4*j2*j0^16+j4^2*g2^2*j2*j0^22+g2^2*j2^5*j0^20+j4^2*g1^4*j2*j0^14)/j2^9/j0^24);
    s :=
	(1/j2^2*j4*j0)^2;

    return
	(e*(x^2+x+s)^3+(a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s),
	(x^2+x+s)^2,
	[a, b, c, d, e, s];

end function;

function Genus3WeierstrassToArtinSchreierModel_T15(f, h)

    Px := Parent(f); x := Px.1;

    f0 := Sqrt(Coefficient(f, 0)); f1 := Sqrt(Coefficient(f, 1));
    f2 := Sqrt(Coefficient(f, 2)); f3 := Sqrt(Coefficient(f, 3));
    f4 := Sqrt(Coefficient(f, 4)); f5 := Sqrt(Coefficient(f, 5));
    f6 := Sqrt(Coefficient(f, 6)); f7 := Sqrt(Coefficient(f, 7));
    f8 := Sqrt(Coefficient(f, 8));

    h0 := Sqrt(Coefficient(((h)), 0));  h1 := Sqrt(Coefficient(((h)), 1));
    h2 := Sqrt(Coefficient(((h)), 2));  h3 := Sqrt(Coefficient(((h)), 3));
    h4 := Sqrt(Coefficient(((h)), 4));


    if h1 ne 0 then
	if h2 ne 0 then

	    a :=
		((f5*h1^4*h2^2+f3*h1^2*h2^4+f1*h2^6+f7*h1^6)/h1^13/h2^20)^2;
	    b :=
		((h0*f7*h1^45+h0^6*f1^2*h1^26*h2^12+h0^6*f5^2*h1^34*h2^4+h0^4*f2^2*h1^32*h2^8+h2^24*h0^16*f1^4+h0^16*f7^4*h1^24+h0^2*f5^2*h1^42+h0*f5*h1^43*h2^2+h0^16*f5^4*h1^16*h2^8+f5*h1^45*h2+f6*h1^46+f4^2*h1^44+h0*f3*h1^41*h2^4+h0^16*f3^4*h1^8*h2^16+h0^2*f1^2*h1^34*h2^8+h0^6*f7^2*h1^38+f2*h1^42*h2^4+h0^6*f3^2*h1^30*h2^8+f3^4*h1^40+f1^4*h1^32*h2^8+f1*h1^41*h2^5+f2^2*h1^40*h2^4+f1^2*h1^38*h2^6+h0^4*f5^2*h1^38*h2^2+f3^2*h1^42*h2^2+h0*f1*h1^39*h2^6+h0^4*f1^2*h1^30*h2^10+h0^4*f6^2*h1^40)/h1^52/h2^16)^2;
	    c :=
		((f5*h1^15*h2^3+h0^4*f1^2*h2^12+f4*h1^14*h2^4+f8*h1^18+h0^4*f5^2*h1^8*h2^4+h0^4*f3^2*h1^4*h2^8+f3*h1^13*h2^5+f1*h1^11*h2^7+f1^2*h1^8*h2^8+f2*h1^12*h2^6+f5^2*h1^16+h0^4*f7^2*h1^12+f6*h1^16*h2^2+f7*h1^17*h2+f0*h1^10*h2^8)/h1^26/h2^24);
	    e :=
		((h0^4*f6*h1^7+h2^2*h0^5*f5*h1^4+h2^4*h0^4*f2*h1^3+h2^4*h0^5*f3*h1^2+h2^6*h0^5*f1+h2*f1*h1^10+h0^5*f7*h1^6+h0*f3*h1^10+f2*h1^11+h2*h0^4*f5*h1^6+h2^2*h0*f1*h1^8+h2^5*h0^4*f1*h1^2)/h1^13)^2;
	    d :=
		(h2^8*(h2*h0^4*f3*h1^21+h0^7*f7*h1^19+h2*h0^6*f5*h1^19+h0^3*f3*h1^23+h0^6*f6*h1^20+h0^4*f4*h1^22+f0*h1^26+h2^4*h0^5*f1*h1^17+h2^4*h0^12*f5^2*h1^8+f1^2*h1^24+h2^2*h0^7*f5*h1^17+h2^12*h0^12*f1^2+h2^4*h0^6*f2*h1^16+h0^2*f2*h1^24+h2^2*h0^3*f1*h1^21+h2^6*h0^8*f2*h1^12+h2*h0^2*f1*h1^23+h0*f1*h1^25+h2^3*h0^4*f1*h1^19+h2^8*h0^12*f3^2*h1^4+h2^5*h0^8*f3*h1^13+h0^5*f5*h1^21+h2^4*h0^8*f4*h1^14+h2^2*h0^4*f2*h1^20+h0^8*f8*h1^18+h2^4*h0^7*f3*h1^15+h2^7*h0^8*f1*h1^11+h2*h0^8*f7*h1^17+h2^3*h0^8*f5*h1^15+h2^5*h0^6*f1*h1^15+h2^8*h0^8*f1^2*h1^8+h2^2*h0^8*f6*h1^16+h0^8*f5^2*h1^16+h2^8*h0^8*f0*h1^10+h0^4*f3^2*h1^20+h2^4*h0^4*f1^2*h1^16+h0^12*f7^2*h1^12+h2^6*h0^7*f1*h1^13)/h1^26);

	    return (a*x^6 + b*x^5 + c*x^4 + e*x + d)*x, x, [a, b, c, d, e];
	end if;

	a :=
	    (1/h1^27*f7)^2;
	b :=
	    ((f6*h1^22+h0^4*f6^2*h1^16+h0^6*f7^2*h1^14+f7^4*h0^16+h0^2*f5^2*h1^18+f3^4*h1^16+f4^2*h1^20+f7*h0*h1^21)/h1^44)^2;
	c :=
	    ((f5^2*h1^4+f7^2*h0^4+f8*h1^6)/h1^38);
	e :=
	    ((f3*h0*h1^4+f2*h1^5+f7*h0^5+f6*h0^4*h1)/h1^7)^2;
	d :=
	    ((h1^9*h0^5*f5+h1^12*f1^2+h1^14*f0+h1^8*h0^4*f3^2+h0^12*f7^2+h1^13*h0*f1+h1^7*h0^7*f7+h1^10*h0^4*f4+f8*h0^8*h1^6+h0^8*f5^2*h1^4+h1^8*h0^6*f6+h1^11*h0^3*f3+h1^12*h0^2*f2)/h1^6);

	return (a*x^6 + b*x^5 + c*x^4 + e*x + d)*x, x, [a, b, c, d, e];
    end if;

    /* h1 = 0 and thus h2 = 0, h0 = 0, h3 <> 0 otherwise, we have a Type (7) curve
   */
   a :=
       (1/h3^7*f1)^2;
   b :=
       ((h3^14*h4^6*f1^2+h3^20*f4^2+f1*h4*h3^21+h3^16*f5^4+h3^18*h4^2*f3^2+h3^16*h4^4*f2^2+f2*h3^22+f1^4*h4^16)/h3^28)^2;
   c :=
       (f0*h3^6+f3^2*h3^4+f1^2*h4^4)/h3^14;
   e :=
       ((f5*h4*h3^4+f6*h3^5+f2*h4^4*h3+f1*h4^5)/h3^7)^2;
   d :=
       (h4^12*f1^2+h4^8*f3^2*h3^4+h4^6*f2*h3^8+h4^5*f3*h3^9+f8*h3^14+f7^2*h3^12+h4*f7*h3^13+h4^7*f1*h3^7+h4^4*f5^2*h3^8+h4^4*f4*h3^10+h4^3*f5*h3^11+h4^2*f6*h3^12+h4^8*f0*h3^6)/h3^14;

   return (a*x^6 + b*x^5 + c*x^4 + e*x + d)*x, x, [a, b, c, d, e];

end function;


function Genus3WeierstrassToArtinSchreierModel_T7(f, h)

    Px := Parent(f); x := Px.1;

    f0 := Sqrt(Coefficient(f, 0)); f1 := Sqrt(Coefficient(f, 1));
    f2 := Sqrt(Coefficient(f, 2)); f3 := Sqrt(Coefficient(f, 3));
    f4 := Sqrt(Coefficient(f, 4)); f5 := Sqrt(Coefficient(f, 5));
    f6 := Sqrt(Coefficient(f, 6)); f7 := Sqrt(Coefficient(f, 7));
    f8 := Sqrt(Coefficient(f, 8));

    h0 := Sqrt(Sqrt(Sqrt(Coefficient(h, 0))));
    h4 := Sqrt(Sqrt(Sqrt(Coefficient(h, 4))));

    if h4 ne 0 then

	a :=
	    ((h0^6*f7+h0^4*f5*h4^2+h0^2*f3*h4^4+f1*h4^6)/h4^7)^2;
	b :=
	    ((h0^5*f7*h4^7+h0^4*f6*h4^8+h0*f3*h4^11+f2*h4^12+h0^4*f7^2+f5^2*h4^4)/h4^14)^2;
	c :=
	    ((h0^4*f7+f3*h4^4)/h4^7)^2;
	d :=
	    (f8*h0^8*h4^48+f7*h0^7*h4^49+f6*h0^6*h4^50+f5*h0^5*h4^51+f4*h0^4*h4^52+f3*h0^3*h4^53+f2*h0^2*h4^54+f1*h0*h4^55+f0*h4^56+h0^6*f7^2*h4^42+h0^4*f6^2*h4^44+h0^2*f5^2*h4^46+f4^2*h4^48+h0^4*f7^4*h4^28+f6^4*h4^32+f7^8)/h4^56;
	e :=
	    (1/h4^8*f8)^2;

	return a*x^7+b*x^6+c*x^5+d*x^4+e, 1+0*x, [a, b, c, d, e];
    end if;

    if h0 ne 0 then

	h0 := h0^8;

	a :=
	    (f7/h0)^2;
	b :=
	    ((f6*h0+f3^2)/h0^2)^2;
	c :=
	    (f5/h0)^2;
	d :=
	    (f8*h0^7+f4^2*h0^6+f2^4*h0^4+f1^8)/h0^8;
	e :=
	    (f0/h0)^2;

	return a*x^7+b*x^6+c*x^5+d*x^4+e, 1+0*x, [a, b, c, d, e];

    end if;

    /* Some formulas, just in case...
   * ...because, this is no more a genus 3 hyperelliptic curve */

   return f7^2*x^7 + f5^2*x^5 + f3^2*x^3 + f1^2*x, 0*x, _;

end function;

function ShiodaInvariantsV4(abcde : normalize := false)

    n0, n1, n2, n3, n4, d0, d1, d2, d3, d4 := Explode(abcde);

    JI := [];

    // I02
    Kx := d2^2 + d1*d3;
    Append(~JI, Kx);

    // I11
    Kx := n3*d1 + n1*d3;
    Append(~JI, Kx);

    // I20
    Kx := n2^2 + n1*n3;
    Append(~JI, Kx);

    // I21
    Kx := n3^2*d0 + n2*n3*d1 + n1*n3*d2 + n1*n2*d3 + n1^2*d4;
    Append(~JI, Kx);

    // I12
    Kx := n4*d1^2 + n3*d1*d2 + n2*d1*d3 + n1*d2*d3 + n0*d3^2;
    Append(~JI, Kx);

    // I03
    Kx := d1*d2*d3 + d0*d3^2 + d1^2*d4;
    Append(~JI, Kx);

    // I30
    Kx := n1*n2*n3 + n0*n3^2 + n1^2*n4;
    Append(~JI, Kx);

    // I22
    Kx :=
	n3*n4*d0*d1 + n2*n4*d1^2 + n3^2*d0*d2 + n2*n3*d1*d2 + n1*n4*d1*d2 + n1*n3*d2^2 +
	n2*n3*d0*d3 + n1*n4*d0*d3 + n2^2*d1*d3 + n1*n2*d2*d3 + n0*n3*d2*d3 +
	n0*n2*d3^2 + n1*n2*d1*d4 + n0*n3*d1*d4 + n1^2*d2*d4 + n0*n1*d3*d4;
    Append(~JI, Kx);

    // I33
    Kx :=
	n3*n4^2*d0^2*d1 + n1*n4^2*d1^3 + n2^2*n3*d1*d2^2 + n1*n3^2*d1*d2^2 +
	n1*n2*n4*d1*d2^2 + n0*n3*n4*d1*d2^2 + n1*n2*n3*d2^3 + n0*n3^2*d2^3 +
	n1^2*n4*d2^3 + n3^3*d0^2*d3 + n1*n4^2*d0^2*d3 + n2^2*n3*d1^2*d3 +
	n1*n2*n4*d1^2*d3 + n0*n3*n4*d1^2*d3 + n2^2*n3*d0*d2*d3 + n1*n3^2*d0*d2*d3 +
	n2^3*d1*d2*d3 + n0*n3^2*d1*d2*d3 + n1^2*n4*d1*d2*d3 + n1*n2^2*d2^2*d3 +
	n1^2*n3*d2^2*d3 + n0*n2*n3*d2^2*d3 + n0*n1*n4*d2^2*d3 + n2^3*d0*d3^2 +
	n1*n2*n3*d0*d3^2 + n1*n2^2*d1*d3^2 + n0*n2*n3*d1*d3^2 + n0*n1*n4*d1*d3^2 +
	n0^2*n3*d3^3 + n2^2*n3*d0*d1*d4 + n1*n3^2*d0*d1*d4 + n2^3*d1^2*d4 +
	n1*n2*n3*d1^2*d4 + n1*n2^2*d1*d2*d4 + n1^2*n3*d1*d2*d4 + n1*n2^2*d0*d3*d4 +
	n1^2*n3*d0*d3*d4 + n1^3*d1*d4^2 + n0^2*n3*d1*d4^2 + n0^2*n1*d3*d4^2;
    Append(~JI, Kx);

    // I44
    Kx :=
	n4^4*d0^4 + n3*n4^3*d0^3*d1 + n2*n4^3*d0^2*d1^2 + n1*n4^3*d0*d1^3 + n0*n4^3*d1^4
	+ n3^2*n4^2*d0^3*d2 + n2*n3*n4^2*d0^2*d1*d2 + n1*n4^3*d0^2*d1*d2 +
	n1*n3*n4^2*d0*d1^2*d2 + n0*n3*n4^2*d1^3*d2 + n2^2*n4^2*d0^2*d2^2 +
	n2^2*n3*n4*d0*d1*d2^2 + n1*n3^2*n4*d0*d1*d2^2 + n1*n2*n4^2*d0*d1*d2^2 +
	n0*n3*n4^2*d0*d1*d2^2 + n2^3*n4*d1^2*d2^2 + n1*n2*n3*n4*d1^2*d2^2 +
	n0*n2*n4^2*d1^2*d2^2 + n2^2*n3^2*d0*d2^3 + n1*n3^3*d0*d2^3 +
	n1^2*n4^2*d0*d2^3 + n2^3*n3*d1*d2^3 + n1*n2*n3^2*d1*d2^3 +
	n1*n2^2*n4*d1*d2^3 + n1^2*n3*n4*d1*d2^3 + n0*n1*n4^2*d1*d2^3 +
	n1*n2^2*n3*d2^4 + n1^2*n3^2*d2^4 + n0^2*n4^2*d2^4 + n3^3*n4*d0^3*d3 +
	n2*n3*n4^2*d0^3*d3 + n1*n4^3*d0^3*d3 + n2*n3^2*n4*d0^2*d1*d3 +
	n1*n3*n4^2*d0^2*d1*d3 + n2^2*n3*n4*d0*d1^2*d3 + n0*n3*n4^2*d0*d1^2*d3 +
	n2^3*n4*d1^3*d3 + n1*n2*n3*n4*d1^3*d3 + n0*n3^2*n4*d1^3*d3 +
	n2^2*n3*n4*d0^2*d2*d3 + n1*n2*n4^2*d0^2*d2*d3 + n0*n3*n4^2*d0^2*d2*d3 +
	n1*n2*n3*n4*d0*d1*d2*d3 + n0*n3^2*n4*d0*d1*d2*d3 + n1^2*n4^2*d0*d1*d2*d3 +
	n1*n2^2*n4*d1^2*d2*d3 + n1^2*n3*n4*d1^2*d2*d3 + n0*n2*n3*n4*d1^2*d2*d3 +
	n0*n1*n4^2*d1^2*d2*d3 + n2^3*n3*d0*d2^2*d3 + n1*n2*n3^2*d0*d2^2*d3 +
	n1*n2^2*n4*d0*d2^2*d3 + n0*n1*n4^2*d0*d2^2*d3 + n2^4*d1*d2^2*d3 +
	n1*n2^2*n3*d1*d2^2*d3 + n0*n1*n3*n4*d1*d2^2*d3 + n1*n2^3*d2^3*d3 +
	n1^2*n2*n3*d2^3*d3 + n0*n2^2*n3*d2^3*d3 + n0*n1*n3^2*d2^3*d3 +
	n0^2*n3*n4*d2^3*d3 + n2^2*n3^2*d0^2*d3^2 + n1*n3^3*d0^2*d3^2 +
	n2^3*n4*d0^2*d3^2 + n1*n2*n3*n4*d0^2*d3^2 + n0*n3^2*n4*d0^2*d3^2 +
	n1^2*n4^2*d0^2*d3^2 + n0*n2*n4^2*d0^2*d3^2 + n1^2*n3*n4*d0*d1*d3^2 +
	n0*n2*n3*n4*d0*d1*d3^2 + n0*n1*n4^2*d0*d1*d3^2 + n2^4*d1^2*d3^2 +
	n1*n2^2*n3*d1^2*d3^2 + n0*n2^2*n4*d1^2*d3^2 + n1*n2^2*n3*d0*d2*d3^2 +
	n1^2*n3^2*d0*d2*d3^2 + n1^2*n2*n4*d0*d2*d3^2 + n0*n1*n3*n4*d0*d2*d3^2 +
	n0*n2^2*n3*d1*d2*d3^2 + n0*n1*n3^2*d1*d2*d3^2 + n0*n1*n2*n4*d1*d2*d3^2 +
	n0^2*n3*n4*d1*d2*d3^2 + n0*n2^3*d2^2*d3^2 + n0*n1*n2*n3*d2^2*d3^2 +
	n0^2*n2*n4*d2^2*d3^2 + n1*n2^3*d0*d3^3 + n1^2*n2*n3*d0*d3^3 +
	n1^3*n4*d0*d3^3 + n0*n1*n2*n4*d0*d3^3 + n0^2*n3*n4*d0*d3^3 + n0*n2^3*d1*d3^3
	+ n0*n1*n2*n3*d1*d3^3 + n0*n1^2*n4*d1*d3^3 + n0^2*n1*n4*d2*d3^3 +
	n0^3*n4*d3^4 + n3^4*d0^3*d4 + n2*n3^3*d0^2*d1*d4 + n2^2*n3*n4*d0^2*d1*d4 +
	n1*n3^2*n4*d0^2*d1*d4 + n1*n2*n4^2*d0^2*d1*d4 + n0*n3*n4^2*d0^2*d1*d4 +
	n2^2*n3^2*d0*d1^2*d4 + n1*n2*n3*n4*d0*d1^2*d4 + n0*n3^2*n4*d0*d1^2*d4 +
	n1^2*n4^2*d0*d1^2*d4 + n2^3*n3*d1^3*d4 + n1*n2*n3^2*d1^3*d4 +
	n0*n3^3*d1^3*d4 + n0*n2*n3*n4*d1^3*d4 + n0*n1*n4^2*d1^3*d4 +
	n2^2*n3^2*d0^2*d2*d4 + n1^2*n4^2*d0^2*d2*d4 + n1*n2*n3^2*d0*d1*d2*d4 +
	n0*n3^3*d0*d1*d2*d4 + n1^2*n3*n4*d0*d1*d2*d4 + n1*n2^2*n3*d1^2*d2*d4 +
	n1^2*n3^2*d1^2*d2*d4 + n0*n2*n3^2*d1^2*d2*d4 + n0*n1*n3*n4*d1^2*d2*d4 +
	n1^2*n3^2*d0*d2^2*d4 + n1*n2^3*d1*d2^2*d4 + n1^2*n2*n3*d1*d2^2*d4 +
	n0*n2^2*n3*d1*d2^2*d4 + n0^2*n3*n4*d1*d2^2*d4 + n1^2*n2^2*d2^3*d4 +
	n1^3*n3*d2^3*d4 + n0^2*n3^2*d2^3*d4 + n2^3*n3*d0^2*d3*d4 +
	n1*n2*n3^2*d0^2*d3*d4 + n0*n3^3*d0^2*d3*d4 + n1*n2^2*n4*d0^2*d3*d4 +
	n1^2*n3*n4*d0^2*d3*d4 + n0*n1*n4^2*d0^2*d3*d4 + n1*n2^2*n3*d0*d1*d3*d4 +
	n0*n2*n3^2*d0*d1*d3*d4 + n1^2*n2*n4*d0*d1*d3*d4 + n0*n1*n3^2*d1^2*d3*d4 +
	n0*n1*n2*n4*d1^2*d3*d4 + n0^2*n3*n4*d1^2*d3*d4 + n1^2*n2*n3*d0*d2*d3*d4 +
	n0*n1*n3^2*d0*d2*d3*d4 + n1^3*n4*d0*d2*d3*d4 + n0*n1*n2*n3*d1*d2*d3*d4 +
	n0^2*n3^2*d1*d2*d3*d4 + n0*n1^2*n4*d1*d2*d3*d4 + n0*n1*n2^2*d2^2*d3*d4 +
	n0*n1^2*n3*d2^2*d3*d4 + n0^2*n2*n3*d2^2*d3*d4 + n0^2*n1*n4*d2^2*d3*d4 +
	n1^2*n2^2*d0*d3^2*d4 + n0*n1*n2*n3*d0*d3^2*d4 + n0^2*n3^2*d0*d3^2*d4 +
	n0*n1^2*n4*d0*d3^2*d4 + n0*n1*n2^2*d1*d3^2*d4 + n0^2*n1*n4*d1*d3^2*d4 +
	n0^2*n1*n3*d2*d3^2*d4 + n0^3*n3*d3^3*d4 + n2^4*d0^2*d4^2 +
	n1*n2^3*d0*d1*d4^2 + n1^2*n2*n3*d0*d1*d4^2 + n0*n2^2*n3*d0*d1*d4^2 +
	n0*n1*n3^2*d0*d1*d4^2 + n1^3*n4*d0*d1*d4^2 + n0^2*n3*n4*d0*d1*d4^2 +
	n1^2*n2^2*d1^2*d4^2 + n0*n2^3*d1^2*d4^2 + n1^3*n3*d1^2*d4^2 +
	n0*n1*n2*n3*d1^2*d4^2 + n0^2*n3^2*d1^2*d4^2 + n0*n1^2*n4*d1^2*d4^2 +
	n0^2*n2*n4*d1^2*d4^2 + n1^2*n2^2*d0*d2*d4^2 + n0^2*n3^2*d0*d2*d4^2 +
	n0*n1*n2^2*d1*d2*d4^2 + n0^2*n2*n3*d1*d2*d4^2 + n0^2*n1*n4*d1*d2*d4^2 +
	n0^2*n2^2*d2^2*d4^2 + n1^3*n2*d0*d3*d4^2 + n0*n1*n2^2*d0*d3*d4^2 +
	n0*n1^2*n3*d0*d3*d4^2 + n0^2*n2*n3*d0*d3*d4^2 + n0^2*n1*n4*d0*d3*d4^2 +
	n0*n1^2*n2*d1*d3*d4^2 + n0^2*n1*n3*d1*d3*d4^2 + n0^2*n1*n2*d2*d3*d4^2 +
	n0^3*n3*d2*d3*d4^2 + n0^3*n2*d3^2*d4^2 + n1^4*d0*d4^3 + n0*n1^3*d1*d4^3 +
	n0^2*n1*n2*d1*d4^3 + n0^3*n3*d1*d4^3 + n0^2*n1^2*d2*d4^3 + n0^3*n1*d3*d4^3 +
	n0^4*d4^4;
    Append(~JI, Kx);

    Wght := [2, 2, 2, 3, 3, 3, 3, 4, 6, 8];

    if normalize eq false then return JI, Wght; end if;
    return WPSNormalize(Wght, JI), Wght;

end function;

function ShiodaInvariantsChar2_T1111(abcde : normalize := false)


    I02, I11, I20, I21, I12, I03, I30, I22, I33, I44 := Explode(ShiodaInvariantsV4(abcde));

    JI := [];

    // j2
    Kx :=
	I02;
    Append(~JI, Kx);

    // j3
    Kx :=
	I03;
    Append(~JI, Kx);

    // J2
    Kx :=
	I11;
    Append(~JI, Kx);

    // J4
    Kx :=
	I22;
    Append(~JI, Kx);

    // J5
    Kx :=
	I02*I21 + I11*I12 + I20*I03;
    Append(~JI, Kx);

    // J6
    Kx :=
	I12^2 + I21*I03;
    Append(~JI, Kx);

    // J8
    Kx :=
	I20*I21*I03 + I02*I20*I22 + I44;
    Append(~JI, Kx);

    // J9
    Kx :=
	I12^3 + I21*I12*I03 + I02*I12*I22 + I11*I03*I22 + I03*I33;
    Append(~JI, Kx);

    // J11
    Kx :=
	I02*I21^2*I12 + I11*I21*I12^2 + I11*I21^2*I03 + I02*I21*I03*I30 + I02*I11*I21*I22 + I02*I20*I12*I22 + I02^2*I30*I22 + I12*I22^2
	+ I02*I21*I33 + I20*I03*I33;
    Append(~JI, Kx);

    // J12
    Kx :=
	I11^3*I21*I12 + I02*I20^2*I21*I03	+ I11*I20^2*I12*I03 + I20^3*I03^2 +
	I02^2*I11*I21*I30 + I02*I11^2*I12*I30 + I02^2*I20*I12*I30 + I02^3*I30^2 +
	+ I11^4*I22 + I02*I21^2*I22 + I20*I12^2*I22 + I02*I12*I30*I22 + I02*I11*I20*I33
	+ I11*I22*I33 + I11^2*I44 + I22*I44;
    Append(~JI, Kx);


    Wght := [2, 3, 2, 4, 5, 6, 8, 9, 11, 12];

    if normalize eq false then return JI, Wght; end if;
    return WPSNormalize(Wght, JI), Wght;

end function;

function ShiodaInvariantsChar2_T113(abcde : normalize := false)

    /* a, b, c, d, s  of degree  1, 1, 1, 1, 1 */
    a, b, c, d, _, s := Explode(abcde);

    /* J2, J3 */
    JI := [1+0*a, 0*a];

    // Deg. 1
    Kx := a;
    Append(~JI, Kx);

    // Deg. 1
    Kx := c;
    Append(~JI, Kx);

    // Deg. 3
    Kx := s*c^2+d^2+c*d;
    Append(~JI, Kx);

    // Deg. 5
    Kx := s^2*c*a^2 + s*c*a^2 + d*a^2 + c*b + d*a;
    Append(~JI, Kx);

    // Deg. 8
    Kx := s^4*a^4 + s^2*a^3 + s*a^3 + s*a^2 + b*a^2 + b^2 + b*a;
    Append(~JI, Kx);

    Wght := [2, 3, 2, 2, 2, 2, 2];

    if normalize eq false then return JI, Wght; end if;
    return WPSNormalize(Wght, JI), Wght;
end function;

function ShiodaInvariantsChar2_T33(abcde : normalize := false)

    /* a, b, c, d, s  of degree  3, 2, -2, -3, 0 */
    a, b, c, d, _, s := Explode(abcde);

    /* J2, J3 */
    JI := [1+0*a, 0*a];

    // Deg. 3
    Kx := s*c^2 + d^2 + d*c;
    Append(~JI, Kx);

    // Deg. 4
    Kx := s*c^2*a + c^2*a^2 + a^4 + c^3 + c^2*b + d^2*a + c^2*a + s*a^2 + a^3
	+ c^2 + b^2 + c*a + b*a;
    Append(~JI, Kx);

    // Deg. 10
    Kx :=
	s^3*c^6*a + s^2*c^6*a^2 + s^2*c^7 + s^2*c^6*b + s^2*d^2*c^4*a + s^2*c^6*a + c^8
	+ s*d^4*c^2*a + s*d^2*c^4*a + s*c^6*a + d^4*c^2*a^2 + s^2*c^4*a^2 +
	d^2*c^4*a^2 + c^6*a^2 + c^4*a^4 + s*c^2*a^5 + c^2*a^6 + d^4*c^3 + d^2*c^5 +
	c^7 + d^4*c^2*b + d^2*c^4*b + c^6*b + d^6*a + s^2*c^4*a + s*c^4*a^2 +
	s^2*c^2*a^3 + s*c^2*a^4 + c^3*a^4 + c^2*b*a^4 + d^2*a^5 + s^2*c^4 + s*c^5 +
	c^6 + s*c^4*b + c^4*b^2 + s*d*c^3*a + s*c^2*b^2*a + d^4*a^2 + s^2*c^2*a^2 +
	d^2*c^2*a^2 + d*c^3*a^2 + c^4*a^2 + c^2*b^2*a^2 + s*d^2*a^3 + s*c^2*a^3 +
	d*c*a^4 + d^2*c^3 + s*c^4 + d*c^4 + c^5 + d^2*c^2*b + d*c^3*b + c^4*b +
	s*c^2*b^2 + c^3*b^2 + c^2*b^3 + d^4*a + d^3*c*a + s*c^3*a + d*c^3*a +
	s*c^2*b*a + d^2*b^2*a + s*d^2*a^2 + s*d*c*a^2 + d^2*c*a^2 + d^2*b*a^2 +
	d*c*a^3 + d^4 + d*c^3 + d^2*b^2 + d*c*b^2 + d^2*c*a + d*c^2*a + d^2*b*a +
	d*c*b*a;
    Append(~JI, Kx);

    Wght := [2, 3, 2, 2, 2];

    if normalize eq false then return JI, Wght; end if;
    return WPSNormalize(Wght, JI), Wght;
end function;

function ShiodaInvariantsChar2_T15(abcde : normalize := false)

    /* a, b, c, d      of degree    5, 4, 3, -1 */
    a, b, c, d, _ := Explode(abcde);

    /* J2, J3 */
    JI := [0*a, 0*a];

    // Deg. 1
    Kx := d eq 0 select 0 else 1/d;
    Append(~JI, Kx);

    // Deg. 3
    Kx := c;
    Append(~JI, Kx);

    // Deg. 4
    Kx := b;
    Append(~JI, Kx);

    // Deg. 5
    Kx := a;
    Append(~JI, Kx);

    Wght := [2, 3, 1, 3, 4, 5];

    if normalize eq false then return JI, Wght; end if;
    return WPSNormalize(Wght, JI), Wght;

end function;

function ShiodaInvariantsChar2_T7(abcde : normalize := false)

    /* a, b, c, d      of degree    7, 6, 5, 4 */
    a, b, c, d, _ := Explode(abcde);

    /* J2, J3 */
    JI := [0*a, 0*a];

    // Deg. 7
    Kx := a;
    Append(~JI, Kx);

    // Deg 32
    Kx := c^4*b^2 + c^5*a + c*b*a^3 + d*a^4;
    Append(~JI, Kx);

    // Deg 40
    Kx := c^8 + b^2*a^4 + c*a^5;
    Append(~JI, Kx);

    Wght := [2, 3, 7, 32, 40];

    if normalize eq false then return JI, Wght; end if;
    return WPSNormalize(Wght, JI), Wght;

end function;

function Genus3WeierstrassToArtinSchreierModel(f, h)

    Px := Parent(f); x := Px.1;

    h0 := Coefficient(h, 0); h1 := Coefficient(h, 1);
    h2 := Coefficient(h, 2); h3 := Coefficient(h, 3);
    h4 := Coefficient(h, 4);

    J3 := h3^2*h0+h3*h2*h1+h4*h1^2;
    J2 := h2^2 + h1*h3;

    if J3 eq 0 then

	if J2 eq 0 then

	    /* h with a root of order 4 */
	    if h1 eq 0 and h2 eq 0 and h3 eq 0 then
		vprintf G3Twists, 1 : "Type (7)\n";
		F, H, _ :=  Genus3WeierstrassToArtinSchreierModel_T7(f, h);
		return F, H;
	    end if;

	    /* h with a root of order 3 */
	    vprintf G3Twists, 1 : "Type (1,5)\n";
	    F, H, _ := Genus3WeierstrassToArtinSchreierModel_T15(f, h);
	    return F, H;

	end if;

	/* h with two roots of order 2 */
	if h1 eq 0 and h3 eq 0 then
	    vprintf G3Twists, 1 : "Type (3,3)\n";
	    F, H, _ :=  Genus3WeierstrassToArtinSchreierModel_T33(f, h);
	    return F, H;
	end if;

	/* h with a single root of order 2 */
	vprintf G3Twists, 1 : "Type (1,1,3)\n";
	F, H, _ :=  Genus3WeierstrassToArtinSchreierModel_T113(f, h);
	return F, H;

    end if;

    /* Generic case, all roots are of order 1 */
    vprintf G3Twists, 1 : "Type (1,1,1,1)\n";
    F, H, _ := Genus3WeierstrassToArtinSchreierModel_T1111(f, h);
    return F, H;

end function;

function ShiodaInvariantsChar2(f, h : normalize := false)

    Px := Parent(f); x := Px.1;

    h0 := Coefficient(h, 0); h1 := Coefficient(h, 1);
    h2 := Coefficient(h, 2); h3 := Coefficient(h, 3);
    h4 := Coefficient(h, 4);

    J3 := h3^2*h0+h3*h2*h1+h4*h1^2;
    J2 := h2^2+h1*h3;

    if J3 eq 0 then

	if J2 eq 0 then

	    /* h with a root of order 4 */
	    if h1 eq 0 and h2 eq 0 and h3 eq 0 then
		vprintf G3Twists, 1 : "Type (7)\n";
		_, _, abcde := Genus3WeierstrassToArtinSchreierModel_T7(f, h);
		return ShiodaInvariantsChar2_T7(abcde : normalize := normalize);

	    end if;

	    /* h with a root of order 3 */
	    vprintf G3Twists, 1 : "Type (1,5)\n";
	    _, _, abcde := Genus3WeierstrassToArtinSchreierModel_T15(f, h);
	    return ShiodaInvariantsChar2_T15(abcde : normalize := normalize);

	end if;

	/* h with two roots of order 2 */
	if h1 eq 0 and h3 eq 0 then
	    vprintf G3Twists, 1 : "Type (3,3)\n";
	    _, _, abcde :=  Genus3WeierstrassToArtinSchreierModel_T33(f, h);
	    return ShiodaInvariantsChar2_T33(abcde : normalize := normalize);
	end if;

	/* h with a single root of order 2 */
	vprintf G3Twists, 1 : "Type (1,1,3)\n";
	_, _, abcde :=  Genus3WeierstrassToArtinSchreierModel_T113(f, h);
	return ShiodaInvariantsChar2_T113(abcde : normalize := normalize);

    end if;

    /* Generic case, all roots are of order 1 */
    vprintf G3Twists, 1 : "Type (1,1,1,1)\n";
    _, _, abcde := Genus3WeierstrassToArtinSchreierModel_T1111(f, h);
    return ShiodaInvariantsChar2_T1111(abcde : normalize := normalize);

end function;

function ShiodaAlgebraicInvariantsChar2(FreeJI, ratsolve)

    FF := Universe(FreeJI);

    /* Type (1,1,1,1) : j2, j3, J5, J6, J8, J9 yields J2, J4, J11, J12 */
    if #FreeJI eq 6 then
	Pg := PolynomialRing(FF, 4);
	J2 := Pg.1; J4 := Pg.2; J11 := Pg.3; J12 := Pg.4;

	/* if ratsolve eq false or not IsFinite(FF) then */
	    g := 1; LG := [ FF!1 ];
	/* else */
	/*     Support := [i : i in [1..#FreeJI] | FreeJI[i] ne 0]; */
	/*     if #Support eq 0 then */
	/* 	g := 1; */
	/*     else */
	/* 	g := Gcd([i+1 : i in Support]); */
	/*     end if; */
	/*     if g ne 1 then */
	/* 	LG := PowerRepresentativesInFiniteFields(FF, g); */
	/*     else */
	/* 	LG := [ FF!1 ]; */
	/*     end if; */
	/* end if; */

	JIs := [];
	for L in LG do
	    j2, j3, J5, J6, J8, J9 :=
		Explode([L^([2, 3, 5, 6, 8, 9][i] div g)*FreeJI[i] : i in [1..#FreeJI]]);

	    RES := [
		j3*J2^2*J4 + j3*J4^2 + J5*J6 + J2*J9,
		j2^2*J2*J4^2 + j3*J2*J4*J5 + J2*J6^2 + J5*J9 + j3*J11,
		j2*J2^2*J4*J5 + j2*J4^2*J5 + J5^3 + J4*J5*J6 + j3*J2^2*J8 + j3*J4*J8 +
		J2^3*J9 + J2*J4*J9 + j2*J2*J11 + j3*J12,
		j2*J2^3*J4*J5 + J2*J5^3 + J2*J4*J5*J6 + j3*J2^3*J8 + J2^4*J9 + J4^2*J9 +
		j2*J2^2*J11 + J6*J11,
		j2*j3*J4^2*J5 + j2^2*J4^2*J6 + j3*J4*J5*J6 + J6^3 + j3^2*J4*J8 + J9^2 +
		j3^2*J12,
		j2*J2^4*J4^2 + j2*J4^4 + J4^2*J5^2 + J2^4*J4*J6 + J4^3*J6 + j2*J2^2*J4*J8 +
		J2^2*J6*J8 + J4*J6*J8 + J2*J5*J11 + j2*J2^2*J12 + J6*J12,
		j2*J2^4*J4*J6 + j2*J4^3*J6 + J2^2*J5^2*J6 + J4*J5^2*J6 + J2^4*J6^2 +
		J4^2*J6^2 + j2^2*J2^2*J4*J8 + j3*J4*J5*J8 + j2*J2^2*J6*J8 + j2*J4*J6*J8
		+ j3*J2^3*J11 + j3*J2*J4*J11 + j2*J2*J5*J11 + J9*J11 + j2^2*J2^2*J12 +
		j3*J5*J12 + j2*J6*J12,
		J2^3*J4*J5*J6 + j2*J2*J4*J5*J8 + J2^4*J4*J9 + J2^2*J4^2*J9 + J2^2*J8*J9 +
		J4*J8*J9 + j2*J4^2*J11 + J5^2*J11 + J2^2*J6*J11 + J4*J6*J11 +
		j3*J2^3*J12 + j2*J2*J5*J12 + J9*J12,
		j2*J2^4*J4^3 + j2*J4^5 + J2^2*J4^2*J5^2 + J4^3*J5^2 + J2^4*J4^2*J6 + J4^4*J6
		+ j2*J2^2*J4^2*J8 + j2*J4^3*J8 + J4*J5^2*J8 + J2^2*J4*J6*J8 +
		J2*J4*J5*J11 + J11^2 + j2*J4^2*J12 + J5^2*J12 + J2^2*J6*J12
		];

	    if ratsolve eq false then return RES; end if;

	    V := Variety(ideal<Pg | RES>);
	    for v in V do
		JIs := ShiodaInvariantsAppend(JIs,
		    WPSNormalize([2, 3, 2, 4, 5, 6, 8, 9, 11, 12],
		    [j2, j3, FF!v[1], FF!v[2], J5, J6, J8, J9, FF!v[3], FF!v[4]]));
	    end for;

	end for;

	return JIs;

    end if;

    /* Type (1,1,3) : j2 <> 0, K, K', K'', K'''' yields j3 = 0, K'''
    or Type (1,5) : j2 = 0, M1, M3, M4, M5 yields j3 = 0

    Type(1,5) is a dim. 3 stratum, but we have to distinguish it from Type(3,3).
    Testing j2 = 0 is an easy way of doing it.
    */
    if #FreeJI eq 5 then

	/* Type (1,1,3) */
	if FreeJI[1] ne 0 then

	    Pg := PolynomialRing(FF); K3 := Pg.1;

	    j2, K0, K1, K2, K4 := Explode(FreeJI);

	    RES := [K3^2*j2^5+K0^2*K1*K3*j2^2+K0*K1*K3*j2^3+K0^4*K2+K0^2*K2*j2^2+K1^2*K4*j2^2];

	    if ratsolve eq false then return RES; end if;

	    RK3 := Roots(RES[1]);
	    JIs := [];
	    for rk3 in RK3 do
		NJI := WPSNormalize(
		    [2, 3, 2, 2, 2, 2, 2],
		    [j2, FF!0, K0, K1, K2, rk3[1]*j2, K4]);
		JIs := ShiodaInvariantsAppend(JIs, NJI);
	    end for;

	    return JIs;

	end if;

	/* Type (1,5) */
	j2, M1, M3, M4, M5 := Explode(FreeJI);
	Pg := PolynomialRing(FF); j3 := Pg.1;

	if ratsolve eq false then return [j3]; end if;

	return [WPSNormalize(
	    [2, 3, 2, 2, 2, 2],
	    [j2, FF!0, M1, M3, M4, M5])];

    end if;

    /* Type (3,3) : j2, L, L', L'' yields j3 = 0 */
    if #FreeJI eq 4 then
	j2, L0, L1, L2 := Explode(FreeJI);
	Pg := PolynomialRing(FF); j3 := Pg.1;

	if ratsolve eq false then return [j3]; end if;
	return [WPSNormalize(
	    [2, 3, 2, 2, 2],
	    [j2, FF!0, L0, L1, L2])];
    end if;

    /* Type (7) : N7, N32, N40 yields j2 = 0, j3 = 0 */
    N7, N32, N40 := Explode(FreeJI);
    Pg := PolynomialRing(FF, 2); j2 := Pg.1; j3 := Pg.2;

    if ratsolve eq false then return [j2, j3]; end if;
    return [WPSNormalize(
	[2, 3, 7, 32, 40],
	[FF!0, FF!0, N7, N32, N40])];

end function;
