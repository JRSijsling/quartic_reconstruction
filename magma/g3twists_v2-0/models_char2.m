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

/*************** Reconstruction ***************/

function TraceOneElement(FF)
    if IsOdd(Degree(FF)) then
	return FF!1;
    end if;
    repeat
	x := Random(FF);
	t := Trace(x);
    until t ne 0;
    return x/t;
end function;

/* Case (1,1,1,1) - C2 :
*/
function G3Char2Models_T1111_C2(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, J2, J4, J5, J6, J8, J9, J11, J12 := Explode(JI);

    d1 := Sqrt(j3);
    d2 := Sqrt(j2);
    d3 := 0;
    d4 := 1;

    n4 := 0;

    if J2 eq 0 then
	n1 := Sqrt(J6) / d1;
	n2 := (d2*n1 + Sqrt(J5)) / d1;
	n3 := 0;

	if n2 ne 0 then 	/* J5*j3+J6*j2 <> 0 */
	    /* n2^4*J5 + n1^6 <> 0, otherwise C2xC2 case */
	    n0 := J8*n2^3/(n2^4*J5 + n1^6);
	    d0 := n0*(d2*n2^2+n0*n2+n1^2)/n2^3;
	else
	    /*J6 <> 0, otherwise C2xC2xC2 case */
	    n0 := 0;
	    d0 := J8 / n1^4;
	end if;
    else
	n0 := (J2^2*d2^3+J4*d1^2+J6*d2)/d1^2/J2;
	n1 := (J2^2*d2^4+J2^2*d2*d1^2+J5*d1^2+J6*d2^2)/J2/d1^3;
	n2 := 0;
	n3 := J2/d1;

	d0 := (d1^2*d2^2*n3^2+d1^2*d2*n1*n3+d1^2*n1^2+J6)/d1^2/n3^2;
    end if;

    h := d4*x^4+d3*x^3+d2*x^2+d1*x+d0;
    f := n4*x^4+n3*x^3+n2*x^2+n1*x+n0;
    f *:= h;

    if geometric then return [ [f, h] ]; end if;

    o := TraceOneElement(FF);
    return [ [f, h],  [f+o*h^2, h]];

end function;

/* Case (1,1,1,1) - C2xC2 :
*/
function G3Char2Models_T1111_C2xC2(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, J2, J4, J5, J6, J8, J9, J11, J12 := Explode(JI);

    /*
    d0 := Sqrt(J8*(J4*j2^2+J5*j3+J6*j2)/J4^3); d1 := Sqrt(j3); d2 := Sqrt(j2); d3 := 0; d4 := 1;
    n0 := 0; n1 := Sqrt(J6/j3); n2 := n1^2/Sqrt(J4); n3 := 0; n4 := 0;
    */

    n4 := 0*j2; n3 := 0*j2; n1 := Sqrt(J6/j3); n2 :=  J6/(j3*Sqrt(J4));
    d3 := 0*j2+0; d4 := 0*j2+1; d1 := Sqrt(j3); d2 := Sqrt(j2);

    /* 2 twists */
    n0 := 0*j2; d0 := Sqrt((n0^4 + n0^2*n2^2*j2 + n0^2*J4 +  J8)/n2^4);

    h := d4*x^4+d3*x^3+d2*x^2+d1*x+d0;
    f := n4*x^4+n3*x^3+n2*x^2+n1*x+n0;
    f *:= h;

    if geometric then return [ [f, h] ]; end if;
    o := TraceOneElement(FF);

    Twists := [ [f, h],  [f+o*h^2, h] ];

    /* 4 twists */
    RR :=  Roots(x^3+j2*x+j3);
    if #RR eq 3 then
	repeat
	    repeat n := Random(FF); until n ne 0;
	    d := (n^2 + n*n2*Sqrt(j2) + n*Sqrt(J4) + Sqrt(J8)) / n2^2;
	until #Roots(d4*x^4+d3*x^3+d2*x^2+d1*x+d0+d) eq 0;
    else
	d := d0;
	Rn := Roots(x^4 + x^2*n2^2*j2 + x^2*J4 + n2^4*d0^2 + J8);
	n := [r[1] : r in Rn | r[1] ne n0][1];
    end if;

    h := d4*x^4+d3*x^3+d2*x^2+d1*x+d;
    f := n4*x^4+n3*x^3+n2*x^2+n1*x+n;
    f *:= h;

    Twists cat:= [ [f, h], [f+o*h^2, h] ];

    return Twists;

end function;

/* Case (1,1,1,1) - C2xC2xC2 :
*/
function G3Char2Models_T1111_C2xC2xC2(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, J2, J4, J5, J6, J8, J9, J11, J12 := Explode(JI);
    s2j8 := Sqrt(Sqrt(J8));

    n4 := s2j8/j3;
    n3 := 0;
    n2 := 0;
    n1 := n3*j2;
    n0 := n2*j2 + n4*j2^2;

    h := x^3 + j2*x + j3;
    f := (n4*x^4+n3*x^3+n2*x^2+n1*x+n0)*h;

    if geometric then return [ [f, h] ]; end if;

    o := TraceOneElement(FF);
    Twists := [ [f, h], [f+o*h^2, h] ];

    /* 2 twists */
    RR := Roots(x^3+x*j2+j3);
    if #RR eq 0 then return Twists; end if;

    /* 4 twists */
    sj2 := Sqrt(j2); sj3 := Sqrt(j3);

    repeat
	repeat l1 := Random(FF); until not l1 in {FF!0};
    until #Roots(x*(x^3+x*sj2+sj3)+l1+0) eq 0;

    h := x^4+sj2*x^2+sj3*x+l1;

    n0 := s2j8; n1 := FF!0; n2 := FF!0; n3 := FF!0; n4 := FF!0;
    f := n4*x^4+n3*x^3+n2*x^2+n1*x+n0; f *:= h;

    Twists cat:= [ [f, h], [f+o*h^2, h] ];

    if #RR eq 1 then return Twists; end if;

    /* 8 twists */
    repeat
	repeat l2 := Random(FF); until not l2 in {FF!0, l1};
    until #Roots(x*(x^3+x*sj2+sj3)+l2+0) eq 0 and
	#Roots(x*(x^3+x*sj2+sj3)+l2+l1) eq 0;

    h := x^4+sj2*x^2+sj3*x+l2;

    n0 := s2j8; n1 := FF!0; n2 := FF!0; n3 := FF!0; n4 := FF!0;
    f := n4*x^4+n3*x^3+n2*x^2+n1*x+n0; f *:= h;

    Twists cat:= [ [f, h], [f+o*h^2, h] ];

    repeat
	repeat l3 := Random(FF); until not l3 in {FF!0, l1, l2};
    until #Roots(x*(x^3+x*sj2+sj3)+l3+0) eq 0 and
	#Roots(x*(x^3+x*sj2+sj3)+l3+l1) eq 0 and
	#Roots(x*(x^3+x*sj2+sj3)+l3+l2) eq 0;

    h := x^4+sj2*x^2+sj3*x+l3;

    n0 := s2j8; n1 := FF!0; n2 := FF!0; n3 := FF!0; n4 := FF!0;
    f := n4*x^4+n3*x^3+n2*x^2+n1*x+n0;
    f *:= h;

    Twists cat:= [ [f, h], [f+o*h^2, h] ];

    return Twists;

end function;

/* Case (1,1,3) - C2 :
*/
function G3Char2Models_T113_C2(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, K0, K1, K2, K3, K4 := Explode(JI);
    K0 /:= j2;  K1 /:= j2;  K2 /:= j2;  K3 /:= j2;  K4 /:= j2; j2 := 1;

    if K1 eq 0 then

	a := K0;
	c := 0;
	d := K3 / (K0^2+K0);
	s := K4 / (K0^4+K0^2);
	b := K4 * (K0^4+K0^2+K4) / K0^2 / (K0+1)^4;

    else

	a := K0;
	c := K1;
	d := 0;
	s := K2 / K1^2;
	b := (K0^2*K1^2*K2+K0^2*K2^2+K1^3*K3) / K1^4;

    end if;

    h := x^2+x+s;
    f := ((a*x^3+b*x^2)*h+c*x+d)*h;

    if geometric then return [ [f, h] ]; end if;

    o := TraceOneElement(FF);
    return [ [f, h], [f+o*h^2, h] ];

end function;

/* Case (1,1,3) - C4 :
*/
function G3Char2Models_T113_C4(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, K0, K1, K2, K3, K4 := Explode(JI);
    K0 /:= j2;  K2 /:= j2;  K4 /:= j2; j2 :=1;

    s := FF!0; a := FF!1; b := Sqrt(K4)+ s^2 + s; c := FF!0; d := Sqrt(K2);
    h := x^2+x+s; f := ((a*x^3+b*x^2)*h +(c*x+d))*h;

    if geometric then return [ [f, h] ]; end if;

    o := TraceOneElement(FF); tb := Trace(b+1);

    Twists := [ [f, h] ];
    if tb eq 0 then Twists cat:= [ [f+o*h^2, h] ]; end if;

    s := o; a := FF!1; b := Sqrt(K4)+ s^2 + s; c := FF!0; d := Sqrt(K2);
    h := x^2+x+s; f := ((a*x^3+b*x^2)*h +(c*x+d))*h;

    Twists cat:= [ [f, h] ];
    if tb eq 0 then Twists cat:= [ [f+o*h^2, h] ]; end if;

    return Twists;

end function;

/* Case (3,3) - C2 :
*/
function G3Char2Models_T33_C2(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, L0, L1, L2 := Explode(JI);

    L0 /:= j2;  L1 /:= j2;  L2 /:= j2; j2 := 1;

    if L0^2+L1 eq 0 then

	d := L0 / Sqrt(L0^3+L0^2+L2);
	a := 1+1/d^2*L0^2+d^2;
	b := (a^2*d+d^3+a*d+d^2+L0)/d;
	c := (d^2+L0)/d;

	s := 0;

    else

	l0 := Sqrt(Sqrt(L0)); l1 := Sqrt(Sqrt(L1)); l2 := Sqrt(Sqrt(L2));

	s := L0*(L0+l1^2)^3/(L0^2+L0*L1+L2);

	c := (L0+l0^2*l1^2+l2^2)/(l0^2+l1)^3;
	a := c^2;
	b := a^2+c+l1^2;
	d := c;

    end if;

    h := (x^2+x+s)^2;
    f := ((a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s);

    if geometric then return [ [f, h] ]; end if;

    o := TraceOneElement(FF);
    return [ [f, h], [f+o*h^2, h] ];

end function;

/* Case (3,3) - C2xC2 :
*/
function G3Char2Models_T33_C2xC2(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, L0, L1, L2 := Explode(JI);

    L0 /:= j2;  L1 /:= j2;  L2 /:= j2; j2 := 1;

    a := 0; b := Sqrt(L1); c := 0; d := Sqrt(L0); s := 0;

    h := (x^2+x+s)^2;
    f := ((a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s);

    if geometric then return [ [f, h] ]; end if;

    o := TraceOneElement(FF);
    Twists := [ [f, h], [f+o*h^2, h] ];

    a := 0; b := Sqrt(L1); c := 0; d := Sqrt(L0); s := o;
    h := (x^2+x+s)^2; f := ((a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s);

    Twists cat:= [ [f, h], [f+o*h^2, h] ];

    return Twists;

end function;

/* Case (3,3) - C2xS3 :
*/
function G3Char2Models_T33_C2xS3(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, L0, L1, L2 := Explode(JI);

    L0 /:= j2;  L1 /:= j2;  L2 /:= j2; j2 := 1;


    a := 0; b := L0; c := 0; d := Sqrt(L0); s := 0;
    f := ((a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s);  h := (x^2+x+s)^2;
    if geometric then return [ [f, h] ]; end if;

    o := TraceOneElement(FF);
    Twists := [ [f, h], [f+o*h^2, h] ];

    if (Degree(FF) mod 2) eq 0 then
	for _u in FF do
	    if #Roots(x^3+(_u^2+_u+s)*x+(_u^2+_u+s)) eq 0 then u := _u; break; end if;
	end for;
	c := Sqrt(L0/(u^2+u+s)); d := u*c; a := c^2; b := c^4+c^2*s+c^2+d^2+c;
	f := ((a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s);  h := (x^2+x+s)^2;
	Twists cat:= [ [f, h], [f+o*h^2, h] ];
    end if;

    a := 0; b := L0; c := 0; d := Sqrt(L0); s := o;
    f := ((a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s);  h := (x^2+x+s)^2;
    Twists cat:= [ [f, h], [f+o*h^2, h] ];

    if (Degree(FF) mod 2) ne 0 then
	for _u in FF do
	    if #Roots(x^3+(_u^2+_u+s)*x+(_u^2+_u+s)) eq 0 then u := _u; break; end if;
	end for;
	c := Sqrt(L0/(u^2+u+s)); d := u*c; a := c^2; b := c^4+c^2*s+c^2+d^2+c;
	f := ((a*x+b)*(x^2+x+s)+(c*x+d))*(x^2+x+s);  h := (x^2+x+s)^2;
	Twists cat:= [ [f, h], [f+o*h^2, h] ];
    end if;

    return Twists;

end function;

/* Case (1,5) - C2 :
*/
function G3Char2Models_T15_C2(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, M1, M3, M4, M5 := Explode(JI);

    d := 1; c := M3 / M1^3; b := M4 / M1^4; a := M5 / M1^5;

    h := x;
    f := ((a*x^5+b*x^4+c*x^3)*x+d)*h;

    if geometric then return [ [f, h] ]; end if;

    o := TraceOneElement(FF);
    return [ [f, h],  [f+o*h^2, h]];

end function;

/* Case (7) - C2 :
*/
function G3Char2Models_T7_C2(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    j2, j3, N7, N32, N40 := Explode(JI);

    a := N7;
    d := N32 / N7^4;
    b := Sqrt(N40 / N7^4);
    c := 0;

    h := 1+0*x;
    f := a*x^7+b*x^6+c*x^5+d*x^4;

    if geometric then return [ [f, h] ]; end if;

    o := TraceOneElement(FF);
    return [ [f, h],  [f+o*h^2, h]];

end function;

/* Case (7) - C2xC7 :
*/
function G3Char2Models_T7_C2xC7(JI : geometric:= false)

    FF:= Universe(JI); x:= PolynomialRing(FF).1;

    h := 1 + 0*x;
    f := x^7;

    if geometric then return [ [f, h] ]; end if;

    if Degree(FF) mod 3 eq 0 then
	Twists := [ [l*f, h] : l in [r[1] : r in Roots(x^7+1)]];
    else
	Twists := [[f, h]];
    end if;

    o := TraceOneElement(FF);
    return [ [tw[1] + e*h^2 , tw[2] ] : tw in Twists, e in [FF| 0, o]];

end function;

function G3Char2Models(JI: geometric:= false, models:= true, descent:= true)

    FF:= Universe(JI);

    j2 := JI[1]; j3 := JI[2];

    twists:= [];

    if j3 ne 0 then

	j2, j3, J2, J4, J5, J6, J8, J9, J11, J12 := Explode(JI);

	if J2 eq 0 and J4 eq 0 and J5 eq 0 and J6 eq 0 and
	    J9 eq 0 and J11 eq 0 and J12 eq 0 then
	    vprintf G3Twists, 1 : "Type 1111 - Automorphism group C2xC2xC2\n";
	    if models then twists:= G3Char2Models_T1111_C2xC2xC2(JI : geometric:= geometric); end if;
	    return twists, SmallGroup(8, 5); /* C2 x C2 x C2 */
	end if;

	if J2 eq 0 and J9 eq 0 and
	    j2*J4^2 + J5^2 + J4*J6 eq 0 and
	    j3*J4^2 + J5*J6 eq 0 and
	    J11 eq 0 and
	    j2^2*J4^2 + j3*J4*J5 + j2*J5^2 + J6^2 eq 0 and
	    J4*J8 + J12  eq 0 then
	    vprintf G3Twists, 1 : "Type 1111 - Automorphism group C2xC2\n";
	    if models then twists:= G3Char2Models_T1111_C2xC2(JI : geometric:= geometric); end if;
	    return twists, SmallGroup(4, 2); /* C2 x C2 */
	end if;

	if models then twists:= G3Char2Models_T1111_C2(JI : geometric:= geometric); end if;
	vprintf G3Twists, 1 : "Type 1111 - Automorphism group C2\n";
	return twists, SmallGroup(2, 1); /* C2 */

    end if;

    /* Now, j3 = 0
     *************/

    /* Case (1, 1, 3) */
    if j2 ne 0 and #JI eq 7 then
	j2, j3, K0, K1, K2, K3, K4 := Explode(JI);

	if K0 eq j2 and K1 eq 0 and K3 eq 0 then
	    vprintf G3Twists, 1 : "Type 113 - Automorphism group C4\n";
	    if models then twists:= G3Char2Models_T113_C4(JI : geometric:= geometric); end if;
	    return twists, SmallGroup(4, 1); /* C4 */
	end if;

	vprintf G3Twists, 1 : "Type 113 - Automorphism group C2\n";
	if models then twists:= G3Char2Models_T113_C2(JI : geometric:= geometric); end if;
	return twists, SmallGroup(2, 1);
    end if;

    /* Case (3, 3) */
    if j2 ne 0 and #JI eq 5 then

	j2, j3, L0, L1, L2 := Explode(JI);
	L0 /:= j2;  L1 /:= j2;  L2 /:= j2;

	if L1 + L0^2 eq 0 and L2 + L0^3 + L0^2 eq 0  then
	    vprintf G3Twists, 1 : "Type 33 - Automorphism group C2xS3\n";
	    if models then twists:= G3Char2Models_T33_C2xS3(JI : geometric:= geometric); end if;
	    return twists, SmallGroup(12, 4); /* C2 x S3 */
	end if;

	if L2 + L1*L0 + L0^2 eq 0 then
	    vprintf G3Twists, 1 : "Type 33 - Automorphism group C2xC2\n";
	    if models then twists:= G3Char2Models_T33_C2xC2(JI : geometric:= geometric); end if;
	    return twists, SmallGroup(4, 2); /* C2 x C2 */
	end if;

	vprintf G3Twists, 1 : "Type 33 - Automorphism group C2\n";
	if models then twists:= G3Char2Models_T33_C2(JI : geometric:= geometric); end if;

	return twists, SmallGroup(2, 1); /* C2 */

    end if;

    /* Now, j2 = 0
     *************/

    /* Case (1, 5) */
    if #JI eq 6 then
	vprintf G3Twists, 1 : "Type 15 - Automorphism group C2\n";
	if models then twists:= G3Char2Models_T15_C2(JI : geometric:= geometric); end if;
	return twists, SmallGroup(2, 1); /* C2 */
    end if;

    /* Case (7) */
    if #JI eq 5 then
	_, _, N7, N32, N40 := Explode(JI);

	if N32 eq 0 and N40 eq 0  then
	    vprintf G3Twists, 1 : "Type 7 - Automorphism group C2xC7\n";
	    if models then twists:= G3Char2Models_T7_C2xC7(JI : geometric:= geometric); end if;
	    return twists, SmallGroup(14, 2);	    /* C2 x C7 */
	end if;

	vprintf G3Twists, 1 : "Type 7 - Automorphism group C2\n";
	if models then twists:= G3Char2Models_T7_C2(JI : geometric:= geometric); end if;
	return twists, SmallGroup(2, 1); /* C2 */
    end if;

    vprintf G3Twists, 1 : "Point at infinity\n";
    return twists, <>;
end function;
