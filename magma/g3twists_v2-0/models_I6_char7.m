//freeze;

/***
 *  Mini Toolboox for reconstructing genus 3 hyperelliptic curves when the
 *  degree 6 invariant J2^3+5*J3^2 vanishes in characteristic 7.
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
 *  Copyright 2014, R. Basson & R. Lercier & C. Ritzenthaler
 */



 function G3Char7Models_I6(JI : geometric:= false)

 FF:= Universe(JI); x:= PolynomialRing(FF).1;
     J2, J3, J4, J5, J6, J7, J8, J9, J10, J11, J13, J14, J15:= Explode(JI);

     D7:= J2^2*J3 + J3*J4 + J2*J5;


     /* J2 = J3 = 0 */
     if J2 eq 0 then

	 if J3 ne 0 then "Hum, J3 must vanish !"; end if;

	 if J4 eq 0 and J5 eq 0 then
	     /* Model a3 = a5 = a4 = a2 = 0  */

	     if J6 eq 0 and J10 eq 0 then
		 error "[models_char7] C2xPGL case trapped in I6 by error at JI = ", JI;

	     elif J6 eq 0 and J10 ne 0 then
		 vprintf G3Twists, 1 : "J2 = J3 = 0, J4 = J5 = 0, J6 = 0, J10 <> 0\n";

		 a0:= 0;
		 a6:= J15/J10;
		 a1:= 1/a6;
		 a8:= 3*a1^2*a6^5*J14/J10^2;

	     else // J6 <> 0
		 vprintf G3Twists, 1 : "J2 = J3 = 0, J4 = J5 = 0, J6, J10 <> 0\n";
		 a6:= 1;
		 a0:=3*J9/(a6^2*J6);

		 Pa1:= a6^21*J6 * x^14 + 5*a6^12*J6^2*J9 * x^8 + 5*a6^3*J9^4 * x^2 + J9^3*J14 + 3*J9*J10*J11^2 + 3*J10^3*J11;
		 Pa1 /:= Coefficient(Pa1, Degree(Pa1));

		 FPa1:= Factorisation(Pa1);
		 Sort(~FPa1, func<x, y | Degree(x[1]) - Degree(y[1])>);
		 Pa1:= FPa1[1,1];

		 if Degree(Pa1) eq 1 then
		     /* Easy, we may find a rational model in this case */
		     a1:= [r[1] : r in Roots(Pa1)][1];
		 else /* Let's go in a degree at most 14 extension */
		     if IsFinite(FF) then K14:= ext<FF | Pa1>; else K14:= quo<Parent(x) | Pa1>; end if;
		     a1:= K14.1; x:= PolynomialRing(K14).1;
		 end if;

		 a8:= (3*a0*a6^4*J8 + a1^2*a6^5*J6)/J6^2;

	     end if;// J6 = J10 = 0

	     return a8*x^8 + a6*x^6 + a1*x + a0;

	 else // J4 <> 0 or J5 <> 0
	     /* Model a2 = a6 = a4 = a3 = 0  */

	     if J4 eq 0 then
	     	 vprintf G3Twists, 1 : "J2 = J3 = 0, J4 = 0, J5 <> 0\n";
		 a0:= J5;
		 a1:= 0;
		 a7:= 2*J8/J5^2;
		 a8:= 2*J7/J5^2;
	     elif J5 eq 0 then
	     	 vprintf G3Twists, 1 : "J2 = J3 = 0, J4 <> 0, J5 = 0\n";
		 a0:= 0;
		 a1:= 2*J4;
		 a7:= 4*J6/J4^2;
		 a8:= 6*J13/J4^4;
	     else
	     	 vprintf G3Twists, 1 : "J2 = J3 = 0, J4 <> 0, J5 <> 0\n";
		 a0:= J5;
		 a1:= 2*J4;
		 a7:= 2*J6^2/J5^2/J4 + 5*J4^2/J5^2 + 2*J8/J5^2;
		 a8:= 3*J4^3/J5^3 + 4*J4*J8/J5^3 + 4*J6^2/J5^3 + 6*J6/J5/J4;
	     end if;

	     return a8*x^8 + a7*x^7 + x^5 + a1*x + a0;

	 end if; // J4 = J5 = 0

     end if; // J2 = J3 = 0


     /* J2 and J3 <> 0 */

     if D7 eq 0 then

	 Ia2a6:= 3*J3^3 + J2^2*J5 + 6*J4*J5 + 6*J3*J6 + J2*J7;
	 Ia0a2:= 6*J3^3 + J2^2*J5 + 2*J3*J6 + 3*J2*J7;

	 if Ia2a6 eq 0 and Ia0a2 eq 0 then
	     vprintf G3Twists, 1 : "D7 = Ia0a2 = Ia2a6 = 0\n";
	     /* a8*x^8 + a7*x^7 + a4*x^4 + a1*x */

	     a4:= 6*J3/J2;
	     a1a7:= (3*J2^2 + 4*J4)/J2;
	     a1:= - (a1a7^7 + 3*a1a7^2*J10 + 3*J7^2 + 6*J6*J8 + 5*J5*J9 + 2*J4*J10 + J3*J11 + a4*J13 + 6*J14)/(J2*J5 + 5*a4*J6 + 3*J7);
	     a8:= 1/a1;
	     a7:= a1a7/a1;

	     return a8*x^8 + a7*x^7 + a4*x^4 + a1*x;


	 elif Ia2a6 eq 0 and Ia0a2 ne 0 then

	     Ia1a7:= (4*J2*J6 + 6*J3*J5 + 6*J4^2)/J3^2;

	     if Ia1a7 eq 0 then
		 vprintf G3Twists, 1 : "Ia0a2 <> 0, Ia1a7 = 0\n";
		 /* a8*x^8 + a7*x^7 + a4*x^4 + a0 */

		 a4:= 6*J3/J2;
		 a0a8:= (4*J2^2 + 3*J4)/J2;
		 a7:= - (a0a8^7 + 4*a0a8^2*J10 + 2*J7^2 + 5*J6*J8 + 4*J5*J9 + 6*J4*J10 + 4*J3*J11 + 4*a4*J13 + J14)/(3*J2*J5 + 4*a4*J6 + J7);
		 a0:= 1/a7;
		 a8:= a0a8/a0;

		 return a8*x^8 + a7*x^7 + a4*x^4 + a0;

	     else //a1a7 <> 0
		 /* a8*x^8 + a7*x^7 + a4*x^4 + a1*x + a0 */
		 vprintf G3Twists, 1 : "Ia0a2 <> 0, Ia1a7 <> 0\n";

		 a4:= 6*J3/J2;

                 Pa:= J2*x^2 + 6*Ia1a7*J2 + 3*J2^2 + 4*J4;
		 Pa /:= Coefficient(Pa, Degree(Pa));

		 FPa:= Factorisation(Pa);
		 Pa:= FPa[1,1];

		 if Degree(Pa) eq 1 then
		     /* Easy, we may find a rational model in this case */
		     a:= [r[1] : r in Roots(Pa)][1];
		 else /* Let's go in a degree 2 extension */
		     if IsFinite(FF) then K2:= ext<FF | Pa>; else K2:= quo<Parent(x) | Pa>; end if;
		     a:= K2.1; x:= PolynomialRing(K2).1;
		 end if;
		 FF:= CoefficientRing(Parent(x));

		 a0:= a;
		 a8:= a;

		 b:= a^3*a4^16;
		 c:= 6*a^2*a4^17*J4 + 5*a^2*a4^16*J5 + 2*a4^16*J2*J5 + 5*a^4*a4^13*J6
		     + 6*a^2*a4^13*J2*J6 + 3*a4^16*J7 + 3*a^2*a4^14*J7 + 6*a^2*a4^13*J8 + 5*a4^14*J9 + 3*a^2*a4^12*J9
		     + 6*a^4*a4^10*J9 + 6*a4^13*J10 + 6*a^2*a4^11*J10 + a^2*a4^10*J11 + a^2*a4^7*J6*J8 + 5*a4^10*J13
		     + 4*a^2*a4^8*J13 + 2*a4^9*J14 + 4*a4^4*J4*J15;

		 Pa1:= x^2 + c/b * x + Ia1a7^4;
		 Pa1 /:= Coefficient(Pa1, Degree(Pa1));

		 FPa1:= Factorisation(Pa1);
		 Pa1:= FPa1[1,1];

		 if Degree(Pa1) eq 1 then
		     /* Easy, we may find a rational model in this case */
		     a1:= [r[1] : r in Roots(Pa1)][1];
		 else /* Let's go in a degree 2 extension */
		     if IsFinite(FF) then K2:= ext<FF | Pa1>; else K2:= quo<Parent(x) | Pa1>; end if;
		     a1:= K2.1; x:= PolynomialRing(K2).1;
		 end if;
		 FF:= CoefficientRing(Parent(x));

		 Pa1:= x^4 - a1;
		 Pa1 /:= Coefficient(Pa1, Degree(Pa1));

		 FPa1:= Factorisation(Pa1);
		 Sort(~FPa1, func<x, y | Degree(x[1]) - Degree(y[1])>);
		 Pa1:= FPa1[1,1];

		 if Degree(Pa1) eq 1 then
		     /* Easy, we may find a rational model in this case */
		     a1:= [r[1] : r in Roots(Pa1)][1];
		 else /* Let's go in a degree at most 4 extension */
		     if IsFinite(FF) then K4:= ext<FF | Pa1>; else K4:= quo<Parent(x) | Pa1>; end if;
		     a1:= K4.1; x:= PolynomialRing(K4).1;
		 end if;

		 a7:= Ia1a7/a1;

		 return a8*x^8 + a7*x^7 + a4*x^4 + a1*x + a0;
	     end if;//Ia1a7 = 0


	 elif Ia2a6 ne 0 and Ia0a2 eq 0 then
	     vprintf G3Twists, 1 : "Ia2a6 <> 0\n";
	     /* a8*x^8 + a7*x^7 + a6*x^6 + a4*x^4 + a1*x */

	     a4:= 6*J3/J2;
	     a6:= (4*a4^2*J5 + 4*J7 + a4*J8/J2 + 3*a4*J9/J3 + 3*a4*J6)/a4^2;
	     a1:= 1/a6;
	     a8:= (6*a6^2*J4^3 + 4*a6^2*J2*J5^2 + 4*a6^2*J2*J4*J6 + 2*a6^2*a4*J4*J7 + 2*a6^2*a4*J3*J8 + 4*a6^2*J5*J7)
		  /(6*J3*J5^2 + 5*J2*J5*J6 + 6*a4*J6^2 + 3*J2*J4*J7 + 5*a4*J5*J7 + 5*J6*J7);
	     a7:= (3*J2^2 + 4*J4)/J2/a1;

	     return a8*x^8 + a7*x^7 + a6*x^6 + a4*x^4 + a1*x;

	 else
	     error "Both Ia2a6 and Ia0a2 are nonzero !";
	 end if;//Ia2a6, Ia0a2


     else //D7 <> 0

	 a6:= 1;
	 a4:= 6*J3/J2;
	 a0:= (4*J3^2 + 2*J2*J4 + 3*a4*J5)/J3;
	 a8:= (2*J2*J3^2 + 3*a0*a4*J4 + 2*a4*J3*J4 + 2*a0*J5 + 4*J3*J5 + 6*J2*J6 + 3*a4*J7)/(J3^3 + 4*J2*J3*J4 + 6*a4*J3*J5);

	 Pa1:= 2*J3 * x^2 + a8*J3^3 + 4*a8*J2*J3*J4 + 6*a8*a4*J3*J5 + 4*J2*J3^2 + a0*a4*J4 + a4*J3*J4 + 2*J4^2 + 6*a0*J5 + 6*J2*J6;
	 Pa1 /:= Coefficient(Pa1, Degree(Pa1));

	 FPa1:= Factorisation(Pa1);
	 Sort(~FPa1, func<x, y | Degree(x[1]) - Degree(y[1])>);
	 Pa1:= FPa1[1,1];

	 if Degree(Pa1) eq 1 then
	     /* Easy, we may find a rational model in this case */
	     a1:= [r[1] : r in Roots(Pa1)][1];
	 else /* Let's go in a degree 2 extension */
	     if IsFinite(FF) then K2:= ext<FF | Pa1>; else K2:= quo<Parent(x) | Pa1>; end if;
	     a1:= K2.1; x:= PolynomialRing(K2).1;
	 end if;

	 if a1 ne 0 then
	     a7:= (4*a8*J2*J3 + 3*a8*a4*J4 + 4*a0*a4 + a4*J3 + 4*a8*J5 + 4*J4)/a1/J2;
	 else
	     if 2*a4*J5*J6 + J2*J3*J7 + 3*a4*J4*J7 + a0*a4*J8 + 3*J5*J7 + 5*J4*J8 + J3*J9 + J2*J10 + 3*a4*J11 ne 0 then
		 Pa7:= x^2 * (2*a4*J5*J6 + J2*J3*J7 + 3*a4*J4*J7 + a0*a4*J8 + 3*J5*J7 + 5*J4*J8 + J3*J9 + J2*J10 + 3*a4*J11)
		       + a0^4*a8 + 6*a8^2*a4*J3*J9 + 6*a0^2*a8*J6 + 5*a8^2*J6*J7 + 3*a8^2*J5*J8 + a8^2*J4*J9 + 4*a8^2*J3*J10 +
		       4*a8^2*J2*J11 + 2*a4*J5^2 + 5*J2*J3*J6 + 2*a4*J4*J6 + a8*J6^2 + 4*a4*J3*J7 + 6*a8*J5*J7 + 4*a8*J4*J8 +
		       6*a0*a8*J9 + 5*a8*J3*J9 + 5*a8*a4*J11 + J5*J6 + 2*J4*J7 + 3*a0*J8 + 4*J2*J9 + 6*J11;

	     else
		 Pa7:= x^2 * (a4*J5^2 + J2*J3*J6 + 5*a4*J4*J6 + 3*a0*a4*J7 + 6*a4*J3*J7 + 4*J5*J6 + 2*J3*J8 + 3*J2*J9)
		       + 4*a8^2*J6^2 + 3*a8^2*J5*J7 + 4*a8^2*J4*J8 + 4*a8^2*J3*J9 + 4*a8^2*J2*J10 + 3*a8^2*a4*J11 + 5*a4*J4*J5 +
		       4*a0*a4*J6 + 4*a4*J3*J6 + 6*a8*J5*J6 + 6*a8*J4*J7 + 6*a0*a8*J8 + 4*a8*J3*J8 + 5*a8*J2*J9 + 3*a8*a4*J10
		       + 5*J5^2 + 5*a0*J7 + 4*J3*J7 + 2*J2*J8 + 3*a8*J11 + 5*J10;
	     end if;

	     Pa7 /:= Coefficient(Pa7, Degree(Pa7));

	     FPa7:= Factorisation(Pa7);
	     Sort(~FPa7, func<x, y | Degree(x[1]) - Degree(y[1])>);
	     Pa7:= FPa7[1,1];

	     if Degree(Pa7) eq 1 then
		 /* Easy, we may find a rational model in this case */
		 a7:= [r[1] : r in Roots(Pa7)][1];
	     else /* Let's go in a degree 2 extension */
		 if IsFinite(FF) then K4:= ext<FF | Pa7>; else K4:= quo<Parent(x) | Pa7>; end if;
		 a7:= K4.1; x:= PolynomialRing(K4).1;
	     end if;

	 end if;

	 return a8*x^8 + a7*x^7 + a6*x^6 + a4*x^4 + a1*x + a0;

     end if; //D7 = 0

 end function;


