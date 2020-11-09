//freeze;

/***
 *  Computing Geometric Isomorphisms between two polynomials of even degree
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
 *  Copyright 2013, R. Lercier, C. Ritzenthaler & J. Sijsling
 */

 /* The definitive algebraic versions

  Etape 1: On ramene f et g en deg 2*n (toujours possible sauf si f et g ont
  pour point   de ramification tout le corps)

  Etape 2: On annule les coeffs en deg. 2*n-1 par la transformation simple.
           x = X - a7*Y/8/a8, y = Y

  Etape 3: on suppose que les deux coeffs diagonaux de l'isomorphisme sont
  non-nuls (et on voit si ca marche sinon, on applique un isomorphisme
  aleatoire a f)

  a7 := 0; b7 := 0;

  f := a0*y^8+a1*x*y^7+a2*x^2*y^6+a3*x^3*y^5+a4*x^4*y^4+a5*x^5*y^3+a6*x^6*y^2+a7*x^7*y+a8*x^8;
  g := b0*Y^8+b1*X*Y^7+b2*X^2*Y^6+b3*X^3*Y^5+b4*X^4*Y^4+b5*X^5*Y^3+b6*X^6*Y^2+b7*X^7*Y+b8*X^8;

  # On cherche les isomorphismes de cette forme.

  EQ := subs(x = 1/m11 * X + m12*Y/m22, y = 1/m11 * m21*X + Y/m22, f) - g;
  EQ  := collect(numer(EQ), [X, Y], distributed);

  # On isole m12 = -subs(y=m21, x=1, diff(f, y)/diff(f, x))

  V12 := factor(isolate(coeff(subs(Y=1, EQ), X^7), m12));

  # deg 8
  subs(x=1, y=m21, f - m11^8*b8);

  # deg 7
  subs(x=1, y=m21, m12 * diff(f, x) + diff(f, y))

  # deg 6
  subs(x=1, y=m21, m12^2 * diff(f, x$2) + 2*m12*diff(f, x, y) + diff(f, y$2)) - 2*m11^6*m22^2*b6;

  # deg 5
  subs(x=1, y=m21, m12^3 * diff(f, x$3) + 3*m12^2*diff(f, x$2, y) + 3*m12*diff(f, x, y$2) + diff(f, y$3)) - 6*m11^5*m22^3*b5;

  # deg 4
  subs(x=1, y=m21,
                  m12^4 * diff(f, x$4)
              + 4*m12^3 * diff(f, x$3, y)
              + 6*m12^2 * diff(f, x$2, y$2)
              + 4*m12   * diff(f, x, y$3)
              +           diff(f, y$4)
       ) - 24*m11^4*m22^4*b4;

*/


/*

  f := a0*y^8+a1*x*y^7+a2*x^2*y^6+a3*x^3*y^5+a4*x^4*y^4+a5*x^5*y^3+a6*x^6*y^2+a7*x^7*y+a8*x^8;
  g := b0*Y^8+b1*X*Y^7+b2*X^2*Y^6+b3*X^3*Y^5+b4*X^4*Y^4+b5*X^5*Y^3+b6*X^6*Y^2+b7*X^7*Y+b8*X^8;


  f := a0*y^10+a1*x*y^9+a2*x^2*y^8+a3*x^3*y^7+a4*x^4*y^6+a5*x^5*y^5+a6*x^6*y^4+a7*x^7*y^3+a8*x^8*y^2+a9*x^9*y+a10*x^10:
  g := b0*Y^10+b1*X*Y^9+b2*X^2*Y^8+b3*X^3*Y^7+b4*X^4*Y^6+b5*X^5*Y^5+b6*X^6*Y^4+b7*X^7*Y^3+b8*X^8*Y^2+b9*X^9*Y+b10*X^10:



  EQ := subs(x = bet*Y, y = gam*X + del*Y, f) - g;
  EQ  := collect(numer(EQ), [X, Y], distributed);

*/

declare verbose IsGL2Equiv, 2;

function CovOrd4Deg2(F)

    f, d, n := Explode(F); n := IntegerRing()!n;

    x := Parent(f).1;
    FF := BaseRing(Parent(f));

    a := func<i | Coefficient(f, i)>;

    // (n-2)!*(2)!*(2)!/(n)!/(n)!

    // 1/4 * sum( (-1)^k*(n-k)!*(k+2)!*a(n-2-k)*a(k) , k = 0..(n-2));
    h0 := FF!1/4 * &+[ (-1)^k*Factorial(n-k)*Factorial(k+2)*a(n-2-k)*a(k) : k in [0..(n-2)]];
    h0 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    //1/4 * sum((-1)^k*(n-k)!*(k+2)!*((n-1-k)*a(n-1-k)*a(k)+(1+k)*a(n-2-k)*a(1+k)), k = 0 .. (n-2))
    h1 := FF!1/4*&+[(-1)^k*Factorial(n-k)*Factorial(k+2)*((n-1-k)*a(n-1-k)*a(k)+(1+k)*a(n-2-k)*a(1+k)) : k in [0 .. (n-2)]] ;
    h1 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    // 1/8 * sum((-1)^k*(n-k)!*(k+2)!*(	(k+2)*(k+1)*a(2+k)*a(n-2-k) +	2*(n-1-k)*(k+1)*a(1+k)*a(n-1-k) +	(n-k)*(n-1-k)*a(k)*a(n-k)), k = 0 .. (n-2))
    h2 := FF!1/8*&+[
	(-1)^k*Factorial(n-k)*Factorial(k+2)*(
	(k+2)*(k+1)*a(2+k)*a(n-2-k) +
	2*(n-1-k)*(k+1)*a(1+k)*a(n-1-k) +
	(n-k)*(n-1-k)*a(k)*a(n-k)
	)
	: k in [0 .. (n-2)]] ;
    h2 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    h3 := FF!1/4*&+[(-1)^k*Factorial(n-k)*Factorial(k+2)*((n-1-k)*a(n-k)*a(k+1)+(1+k)*a(n-1-k)*a(2+k)) : k in [0 .. (n-2)]] ;
    h3 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    h4 := FF!1/4 * &+[ (-1)^k*Factorial(n-k)*Factorial(k+2)*a(n-2-k+2)*a(k+2) : k in [0..(n-2)]];
    h4 *:= Factorial(n-2)*Factorial(2)*Factorial(2)/Factorial(n)/Factorial(n);

    return [* h4 * x^4 + h3 * x^3 + h2 * x^2 + h1 * x + h0, 2*d, 4 *];

end function;

function TransformPolynomial(f,n,mat)
    a,b,c,d := Explode(mat);
    x1 := a*Parent(f).1 + b; z1 := c*Parent(f).1 + d;
    return &+[Coefficient(f,i)*x1^i*z1^(n-i) : i in [0..n]];
end function;

function MyRandom(FF : BD := 7)
    if Characteristic(FF) eq 0 then
	return Random(-BD, BD);
    end if;
    return Random(FF);
end function;

/*
function GeometricRootsNew(f);
    R := Parent(f); K := BaseRing(R);
    S := PolynomialRing(K, 1);
    h := hom< R -> S | S.1 >;
    A := AffineSpace(S);
    return [ pt[1] : pt in PointsOverSplittingField(Scheme(A, h(f))) ];
end function;
*/

procedure GeometricRoots(f, ~LST : geometric := true, commonfield := false)

    vprintf IsGL2Equiv, 2 : "Working on %o\n", f;

    /* Single splitting field extension */
    if commonfield then
        _, Rts := SplittingField(f);
        for r in Rts do Append(~LST, r); end for;
        return;
    end if;

    Q := CoefficientRing(f); X := Parent(f).1;
    g := f;


    Rts := Roots(f);
    for r in Rts do
	Append(~LST, r[1]);
	g := g div (X-r[1])^r[2] ;
    end for;

    vprintf IsGL2Equiv, 2 : "Non rational part is %o\n", g;

    /* Repeated extension (by roots of polynomials over the original base field) */
    if geometric eq true then
	Fct := Factorization(g);
	for fct in Fct do
            vprintf IsGL2Equiv, 2 : "Factor = %o\n", fct;
            $$(PolynomialRing(ext<Q | fct[1]>)!fct[1], ~LST : commonfield := commonfield);
            //$$(PolynomialRing(SplittingField(fct[1]))!fct[1], ~LST : commonfield := commonfield);
	end for;
    end if;

end procedure;

function CheckResult(MF, f, F, deg)

    RM := [* *];
    d := Max(Degree(f), Degree(F));

    for L in MF do

	FF := Parent(L[1]);

	fp := PolynomialRing(FF)!f;
	Fp := PolynomialRing(FF)!F;

	_F := TransformPolynomial(fp, deg, L);

        /* Check equality up to leading coefficients */
	if _F * Coefficient(Fp, d) eq Fp * Coefficient(_F, d) then
	    Append(~RM, L);
	end if;

    end for;

    return RM;

end function;


function IsGL2GeometricEquivalentAlphaEq0(_f, _F, d : geometric := true, commonfield := false)

    Q := BaseRing(Parent(_f)); Z := PolynomialRing(Q).1;

    if not IsInvertible(Q!d) then
        vprintf IsGL2Equiv, 1 : "Unable to invert the degree of the form in the field, I give up\n";
        return true, [**];
    end if;

    a0  := Coefficient(_f, 0); a1  := Coefficient(_f, 1);
    a2  := Coefficient(_f, 2); a3  := Coefficient(_f, 3);

    bm0 := Coefficient(_F, d);   bm1 := Coefficient(_F, d-1);
    bm2 := Coefficient(_F, d-2); bm3 := Coefficient(_F, d-3);

    if a0 eq 0 then
	vprintf IsGL2Equiv, 1 : "a0 cannot be equal to zero with an isomorphism with diagonal 0\n";
	return false, [**];
    end if;

    EQ2 :=
	bm0^2*(-d*a1^2+a1^2+2*a2*d*a0)*Z^2
	-a0^2*(2*bm2*d*bm0+bm1^2-d*bm1^2);

    EQ3 :=
	2*bm0^3*(-3*d*a1^3+3*a3*d^2*a0^2+2*a1^3-3*a2*d^2*a0*a1+d^2*a1^3+6*a2*d*a0*a1)*Z^3+
	3*a0*(d-2)*bm1*bm0^2*(-d*a1^2+a1^2+2*a2*d*a0)*Z^2 -
	a0^3*(6*bm3*d^2*bm0^2-2*bm1^3-d^2*bm1^3+3*d*bm1^3);

    PG := GCD(EQ2, EQ3);

    vprintf IsGL2Equiv, 1 : "GCD = %o\n", PG;
    vprintf IsGL2Equiv, 1 : "It is of degree %o\n", Degree(PG);

    if PG eq 0 then
	vprintf IsGL2Equiv, 1 : "HUM... No algebraic condition found on beta, I give up\n";
	vprintf IsGL2Equiv, 1 : "\n";
	return true, [**];
    end if;

    if Degree(PG) eq 0 then
	vprintf IsGL2Equiv, 1 : "No such isomorphism possible\n";
	vprintf IsGL2Equiv, 1 : "\n";
	return false, [**];
    end if;

    GF := [* *]; GeometricRoots(PG, ~GF : geometric := geometric, commonfield := commonfield);
    //GF := GeometricRootsNew(PG);

    ret := false; LST := [**];
    for bet in GF do

	vprintf IsGL2Equiv, 1 : "handling RootOf(%o)\n", MinimalPolynomial(bet);

	EF := Parent(bet);
	Z := PolynomialRing(EF).1;

	del := (bm1 * a0 - a1 * bet * bm0) / bm0 / a0 / d;

	L := [EF | 0, bet, 1, del];

	RM := CheckResult([* L *], _f, _F, d);

	if #RM ne 0 then

	    LF := RM[1];

	    FF := Q;
            /*
	    if Parent(LF[1]) ne FF then
		FF := sub< Parent(LF[1]) | LF>;
		LF := [FF!l : l in LF];
	    end if;
            */
	    if Index(LST, LF) eq 0 then
	        vprintf IsGL2Equiv, 1 :  "%o\n", LF;
		Append(~LST, LF);
	    end if;

	end if;

	ret or:= #RM ne 0;
    end for;

    return ret, LST;

end function;

function IsGL2GeometricEquivalentHeart(_f, _F, deg : geometric := true, commonfield := false)

    Q := BaseRing(Parent(_f));
    Z := Parent(_f).1;

    if not IsInvertible(Q!deg) then
        vprintf IsGL2Equiv, 1 : "Unable to invert the degree of the form in the field, I give up\n";
        return true, [**];
    end if;

    P1 := ProjectiveSpace(Q, 1);
    x  := P1.1; y := P1.2;

    f1 := &+[ Coefficient(_f,j)*x^j*y^(deg-j) : j in [0..deg]];
    F := &+[ Coefficient(_F,j)*x^j*y^(deg-j) : j in [0..deg]];

    /* Set the (deg-1)-th coefficient of F  */
    M12 := MonomialCoefficient(F, x^(deg-1)*y );
    if M12 eq 0 then
	M21 := Q!0; f2 := F;
    else
	M12 := -M12 / ( deg * MonomialCoefficient(F,x^deg) );
	M21 := Q!0;
	f2 := Evaluate(F, x, x + M12*y);
    end if;

    vprintf IsGL2Equiv, 1 : "f2 is %o\n", f2;

    // F2 := UnivariatePolynomial(Evaluate(CoordinateRing(P1)!f2, y, 1));
    bm0 := MonomialCoefficient(f2, x^deg);
    bm2 := MonomialCoefficient(f2, x^(deg-2)*y^2);
    bm3 := MonomialCoefficient(f2, x^(deg-3)*y^3);
    if deg gt 3 then
	bm4 := MonomialCoefficient(f2, x^(deg-4)*y^4);
    end if;

    // deg coeff.
    // Evaluate(f1, [1, m21])-m11^deg*bm0;

    // deg - 1 coeff.
    // Evaluate(m12*Derivative(f1, 1, x) + Derivative(f1, 1, y), [1, m21]);

    // deg - 2 coeff.
    // Evaluate(Nm2*Evaluate(f1, [1, Z]), m21) - 2*m11^(deg-2)*m22^2*bm2*Evaluate(Derivative(f1, 1, x), [1, m21])^2;
    Nm2 := Evaluate(
	      Derivative(f1, 2, x) * Derivative(f1, 1, y)^2
	- 2 * Derivative(f1, 1, x) * Derivative(f1, 1, y) * Derivative(Derivative(f1, 1, x), 1, y)
	+     Derivative(f1, 2, y) * Derivative(f1, 1, x)^2,
	[1, Z]) div  Evaluate(f1, [1, Z]);
	vprintf IsGL2Equiv, 1 : "Nm2 is of degree %o\n", Degree(Nm2);

    if deg gt 3 then

	// deg - 4 coeff.
	// Evaluate(Nm4*Evaluate(f1, [1, Z]), m21) - 24*m11^(deg-4)*m22^4*bm4*Evaluate(Derivative(f1, 1, x), [1, m21])^4;
	Nm4 := Evaluate(
	    Derivative(f1, 4, x) * Derivative(f1, 1, y)^4
	    - 4 * Derivative(Derivative(f1, 3, x), 1, y) * Derivative(f1, 1, y)^3 * Derivative(f1, 1, x)
	    + 6 * Derivative(Derivative(f1, 2, x), 2, y) * Derivative(f1, 1, y)^2 * Derivative(f1, 1, x)^2
	    - 4 * Derivative(Derivative(f1, 1, x), 3, y) * Derivative(f1, 1, y)   * Derivative(f1, 1, x)^3
	    +     Derivative(f1, 4, y) * Derivative(f1, 1, x)^4,
	    [1, Z]) div Evaluate(f1, [1, Z]);
	vprintf IsGL2Equiv, 1 : "Nm4 is of degree %o\n", Degree(Nm4);

	// Evaluate(6*bm0*bm4*Nm2^2 - bm2^2 * Nm4, m21);
	EQ1 := 6*bm0*bm4*Nm2^2 - bm2^2 * Nm4;
	vprintf IsGL2Equiv, 1 : "EQ1 is of degree %o\n", Degree(EQ1);

/*
	if Degree(EQ1) eq -1 then
	    vprintf IsGL2Equiv, 1 : "No algebraic condition given by the first equation, I give up\n";
	    vprintf IsGL2Equiv, 1 : "\n";
	    return true, [**];
	end if;
*/
    end if;

    // deg - 3 coeff.
    // Evaluate(Nm3*Evaluate(f1, [1, Z]), m21) - 6*m11^(deg-3)*m22^3*bm3*Evaluate(Derivative(f1, 1, x), [1, m21])^3;
    Nm3 := Evaluate(
-     Derivative(f1, 3, x) * Derivative(f1, 1, y)^3
+ 3 * Derivative(Derivative(f1, 2, x), 1, y) * Derivative(f1, 1, y)^2 * Derivative(f1, 1, x)
- 3 * Derivative(Derivative(f1, 1, x), 2, y) * Derivative(f1, 1, y)   * Derivative(f1, 1, x)^2
+     Derivative(f1, 3, y) * Derivative(f1, 1, x)^3,
        [1, Z]) div Evaluate(f1, [1, Z]);
vprintf IsGL2Equiv, 1 : "Nm3 is of degree %o\n", Degree(Nm3);

    // Evaluate(9*bm0* bm3^2*Nm2^3 - 2*bm2^3 * Nm3^2, m21);
    EQ2 := 9*bm0* bm3^2*Nm2^3 - 2*bm2^3 * Nm3^2;
vprintf IsGL2Equiv, 1 : "EQ2 is of degree %o\n", Degree(EQ2);

    if deg gt 3 then PG := GCD(EQ1, EQ2); else PG := EQ2; end if;

    vprintf IsGL2Equiv, 1 : "GCD = %o\n", PG;
    vprintf IsGL2Equiv, 1 : "It is of degree %o\n", Degree(PG);

    if PG eq 0 then
	vprintf IsGL2Equiv, 1 : "No algebraic condition found on gamma, I give up\n";
	vprintf IsGL2Equiv, 1 : "\n";
	return true, [**];
    end if;

    if Degree(PG) eq 0 then
	vprintf IsGL2Equiv, 1 : "No such isomorphism possible\n";
	vprintf IsGL2Equiv, 1 : "\n";
	return false, [**];
    end if;

    GF := [* *]; GeometricRoots(PG, ~GF : geometric := geometric, commonfield := commonfield);
    //GF := GeometricRootsNew(PG);

    LST := [**];
    for m21 in GF do

	EF := Parent(m21); Z := PolynomialRing(EF).1;

	PEF := ProjectiveSpace(EF, 1);
	X := PEF.1; Y := PEF.2;

	F1 := &+[ MonomialCoefficient(f1,x^j*y^(deg-j))*X^j*Y^(deg-j) : j in [0..deg]];
	F2 := &+[ MonomialCoefficient(f2,x^j*y^(deg-j))*X^j*Y^(deg-j) : j in [0..deg]];

	vprintf IsGL2Equiv, 1 : "\n";
	vprintf IsGL2Equiv, 1 : "**************************************************************\n";
	vprintf IsGL2Equiv, 1 : "Testing RootOf(%o)\n", MinimalPolynomial(m21);
	vprintf IsGL2Equiv, 1 : "gamma =  %o\n", m21;

	if Evaluate(Derivative(F1, 1, X), [1, m21]) eq 0 then
	    vprintf IsGL2Equiv, 1 : "HUM the derivative in m21 = 0, I give up\n";
	    return true, [**];
	end if;

	m12 := - Evaluate(Derivative(F1, 1, Y), [1, m21]) / Evaluate(Derivative(F1, 1, X), [1, m21]);

	vprintf IsGL2Equiv, 1 : "Then beta = %o\n", m12;

	// Let us check the compatibility conditions
	g1 := Evaluate(F1, [X + m12*Y, m21*X + Y]);
	_<w> := Parent(g1);

	for i := 1 to deg-1 do

	    am1 := MonomialCoefficient(g1, X^(i-1)*Y^(deg-i+1));
	    am0 := MonomialCoefficient(g1, X^(i)*Y^(deg-i));
	    ap1 := MonomialCoefficient(g1, X^(i+1)*Y^(deg-i-1));

	    bm1 := MonomialCoefficient(F2, X^(i-1)*Y^(deg-i+1));
	    bm0 := MonomialCoefficient(F2, X^(i)*Y^(deg-i));
	    bp1 := MonomialCoefficient(F2, X^(i+1)*Y^(deg-i-1));

	    if am1*ap1*bm0^2 - bm1*bp1*am0^2 ne 0 then
		vprintf IsGL2Equiv, 1 : "bad compatibility conditions I ? I give up\n";
		continue m21;
	    end if;

	end for;

	/* Looking for non-zero coeffs in f2 */
	degs := [j : j in [2..deg] | MonomialCoefficient(F2, X^(deg-j)*Y^j) ne 0];
	g, U := XGCD(degs);
	if g ne 1 then
	    vprintf IsGL2Equiv, 1 : "HUM g =  %o\n", g;
	    //		return [**];
	end if;

	/* Are there corresponding coefficients in g1 non-zero ? */
	for d := 0 to deg do

	    if ((MonomialCoefficient(g1, X^(deg-d)*Y^d) eq 0 and
		MonomialCoefficient(F2, X^(deg-d)*Y^d) ne 0) or
		(MonomialCoefficient(g1, X^(deg-d)*Y^d) ne 0 and
		MonomialCoefficient(F2, X^(deg-d)*Y^d) eq 0)) then

		vprintf IsGL2Equiv, 1 : "bad compatibility conditions II ? I give up\n";
		vprintf IsGL2Equiv, 1 : "F2 = %o\n", F2;
		vprintf IsGL2Equiv, 1 : "g1 = %o\n", g1;
		continue m21;
	    end if;
	end for;

	m := MonomialCoefficient(g1, X^(deg)) / MonomialCoefficient(F2, X^(deg));

	R :=
	    &*[ (m * MonomialCoefficient(F2, X^(deg-degs[j])*Y^degs[j]))^U[j]: j in [1..#degs]]
	    /
	    &*[ MonomialCoefficient(g1, X^(deg-degs[j])*Y^degs[j])^U[j]: j in [1..#degs]];

	vprintf IsGL2Equiv, 1 : "R = %o\n", R;
	RR := [* *]; GeometricRoots(Z^g - R, ~RR : geometric := geometric, commonfield := commonfield);

	vprintf IsGL2Equiv, 1 : "F2 = %o\n", F2;
	vprintf IsGL2Equiv, 1 : "g1 = %o\n", g1;

	for RL in RR do

	    EF3 := Parent(RL); Z := PolynomialRing(EF3).1;

	    Mat :=
		1/(1 - M12*M21) *
		Matrix(2, 2, [1, RL * m12, m21, RL]) *
		Matrix(2, 2, [1, -M12, -M21, 1]);

	    Mat *:= 1 / Mat[1,1];

	    FF := Q; LF := Eltseq(Mat);

	    RM := CheckResult([* LF *], _f, _F, deg);

	    if #RM ne 0 then

               /*
	       if Parent(LF[1]) ne FF then
	          FF := sub< Parent(LF[1]) | LF>;
		  LF := [FF!l : l in LF];
	       end if;
               */
	       if Index(LST, LF) eq 0 then
	          vprintf IsGL2Equiv, 1 : "%o\n", LF;
		  Append(~LST, LF);
	       end if;

	    end if;

	end for;

    end for;

    return #LST ne 0, LST;

end function;

function IsGL2GeometricEquivalentMain(_f, _F, deg : geometric := true, commonfield := false)

    PX := Parent(_f);

    vprintf IsGL2Equiv, 1 : "\n\n";
    vprintf IsGL2Equiv, 1 : "------------------------------\n";
    vprintf IsGL2Equiv, 1 : " f = %o\n", _f;
    vprintf IsGL2Equiv, 1 : " F = %o\n", _F;

    ret, MF0 := IsGL2GeometricEquivalentAlphaEq0(_f, _F, deg : geometric := geometric, commonfield := commonfield);
    /* ??? */
    if ret eq true and #MF0 eq 0 then
	return ret, MF0;
    end if;

    vprintf IsGL2Equiv, 1 : "After the Alpha = 0 step\n";
    vprintf IsGL2Equiv, 1 : "ret = %o, MF = %o\n", ret, MF0;

    retp, MFp := IsGL2GeometricEquivalentHeart(_f, _F, deg : geometric := geometric, commonfield := commonfield);
    /* ??? */
    if retp eq true and #MFp eq 0 then
        return retp, MFp;
    end if;

    if commonfield then
        Fields := [**]; for Iso in MF0 cat MFp do
            if Index(Fields, Universe(Iso)) eq 0 then Append(~Fields, Universe(Iso)); end if;
        end for;
        if #Fields ne 1 then
            /* ??? */
            K, Rs := SplittingField([DefiningPolynomial(K) : K in Fields]);
            "... splitting done\n";
            PHIs := [hom< Fields[i]->K | Rs[i][1] > : i in [1..#Fields]];
        else

        end if;
    end if;

    MF := [**];
    for L in MF0 cat MFp do
        _L := L;
        if commonfield and #Fields ne 1 then
            _L :=  [ PHIs[Index(Fields, Universe(L))](l) : l in L];
        end if;
        if Index(MF, _L) eq 0 then Append(~MF, _L); end if;
    end for;

    ret or:= retp;

    return ret, MF;
end function;


intrinsic IsGL2GeometricEquivalent(_f::RngUPolElt, _F::RngUPolElt, deg::RngIntElt: geometric := true, commonfield := false) -> BoolElt, SeqEnum
    {}

    Q := BaseRing(Parent(_f));

    ret := true; MF := [**];

    /* Covariant reduction, when possible */
    p := Characteristic(Q) eq 0 select Infinity() else Characteristic(Q);

    if Degree(_f) gt 4 and Degree(_f) lt p and
       Degree(_F) gt 4 and Degree(_F) lt p then

        vprintf IsGL2Equiv, 1 : "Covariant reduction step\n";
	Cf := CovOrd4Deg2([* _f, 1, deg *])[1];
	CF := CovOrd4Deg2([* _F, 1, deg *])[1];

	if Degree(Cf) ge 3 and Discriminant(Cf) ne 0 and
	    Degree(CF) ge 3 and Discriminant(CF) ne 0 then

	    ret, MF := $$(Cf, CF, 4 : geometric := geometric, commonfield := commonfield);
	    return ret, CheckResult(MF, _f, _F, deg);

	end if;
    else
        vprintf IsGL2Equiv, 1 : "Covariant reduction is not possible\n";
    end if;

    /* Main algorithm */
    nbtry := 0;
    while ret eq true and #MF eq 0 and nbtry lt 10 do

	nbtry +:= 1;

        f := _f; F := _F; ML := IdentityMatrix(Q, 2);
        if nbtry ne 1 then
            repeat
                ML := Matrix(2, 2, [Q | MyRandom(Q : BD := Degree(_f)+1) : i in [1..4]]);
            until &*Eltseq(ML) ne 0 and Determinant(ML) ne 0;
            f  := TransformPolynomial(_f, deg, Eltseq(ML));
            F  := TransformPolynomial(_F, deg, Eltseq(ML));
        end if;

        vprintf IsGL2Equiv, 1 : "ML is %o\n", ML;

	if Degree(f) ne deg or Degree(F) ne deg then continue; end if;

        MLi := ML^(-1);

	ret, MFp := IsGL2GeometricEquivalentMain(f, F, deg : geometric := geometric, commonfield := commonfield);

	MF := [* *];
        for LF in MFp do
            M := Matrix(2, 2, LF);
            /* The test cannot fail, but the "IsSubfield" call is necessary
               to make (sometimes) Q recognize as a subfield of CoefficientRing(M) */
            if not IsSubfield(Q, CoefficientRing(M)) then
                ret := false; break;
            end if;
            TM := ML * M * MLi;
	    if TM[1, 1] ne 0 then TM /:= TM[1, 1]; end if;
	    Append(~MF, Eltseq(TM));
	end for;

    end while;

    /* Classical one in the very rare cases where nothing else was possible
       (this may happen on very small finite fields) */
    if (ret eq true and #MF eq 0) and geometric then
	SF := Compositum(SplittingField(_f), SplittingField(_F));
	ret, MF := IsGL2Equivalent(PolynomialRing(SF)!_f, PolynomialRing(SF)!_F, deg);
    end if;

    if geometric then
        return ret, MF;
    end if;

    /*
    if geometric then
        if ret and (Type(Q) eq FldRat) then
            L := Universe(MF[1]);
            L0, h := Polredabs(L);
            MF := [ [ h(c) : c in mf ] : mf in MF ];
        end if;
        return ret, MF;
    end if;
    */

    /* Non-geometric case */
    return IsGL2Equivalent(_f, _F, deg);

end intrinsic;
