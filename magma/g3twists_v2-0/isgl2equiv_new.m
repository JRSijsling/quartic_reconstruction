Attach( "isgl2equiv.m");

/*
This is a generic procedure to find an isomorphism between two binary forms of degree n.
Restrictions are:
- the leading coefficient is not 0 for the two forms
- characteristic of the field does not divides n
- the matrix of transformation [a,b,c,d] when the two forms are put in the shape x^n+ 0*x^(n-1)*z+...is such that a d <>0

*/

function DerivativeExpression(f1,f2,i)
	P<x,z>:=Parent(f1);
	FF:=BaseRing(P);
	n:=Degree(f1);
	N:=0;
	for j:=0 to i do
	N:=N+Binomial(i,j)*(-Derivative(f2,1,z))^j*Derivative(f2,1,x)^(i-j)*Derivative(Derivative(f2,j,x),i-j,z);
	end for;
	return N div f2,Factorial(i)*MonomialCoefficient(f1,x^(n-i)*z^i);
end function;


function IsGL2GenericEquivalent(F1, F2)
	P<x,z>:=Parent(F1);
	FF:=BaseRing(P);
	n:=Degree(F1);
	if MonomialCoefficient(F2,x^n) eq 0 or MonomialCoefficient(F1,x^n) eq 0 then
		return "need the x^n coefficient of F2 and F1 to be non zero";
	else
		f2:=F2/MonomialCoefficient(F2,x^n);
		f1:=F1/MonomialCoefficient(F1,x^n);
	end if;
	if Characteristic(FF) ne 0 and (n mod Characteristic(FF)) eq 0 then
		if MonomialCoefficient(f2,x^(n-1)*z) ne 0 or MonomialCoefficient(f1,x^(n-1)*z) ne 0 then
			return "not possible to put the x^(n-1)z coefficient of the polynomial F2 and F1 to 0";
		else
			M1:=Matrix([[1,0],[0,1]]);
			M2:=Matrix([[1,0],[0,1]]);
		end if;
	else
		M2:=Matrix([[1,-MonomialCoefficient(f2,x^(n-1)*z)/n],[0,1]]);
		f2:=Evaluate(f2,[x-MonomialCoefficient(f2,x^(n-1)*z)/n*z,z]);
		M1:=Matrix([[1,MonomialCoefficient(f1,x^(n-1)*z)/n],[0,1]]);
		f1:=Evaluate(f1,[x-MonomialCoefficient(f1,x^(n-1)*z)/n*z,z]);
	end if;
	N21,N22:=DerivativeExpression(f1,f2,2);
	N31,N32:=DerivativeExpression(f1,f2,3);
	N41,N42:=DerivativeExpression(f1,f2,4);
	N51,N52:=DerivativeExpression(f1,f2,5);
//	print N51,N52;
	P2<u>:=PolynomialRing(FF);
	phi:=hom<P-> P2 | 1,u>;
	Eqc:=Gcd(phi(N21^2*N42-N41*N22^2),phi(N21^3*N32^2-N31^2*N22^3));
//	Eq2c:=Gcd(phi(N21^5*N52^2-N51^2*N22^5),phi(N21^3*N32^2-N31^2*N22^3));
//	Eq3c:=Gcd(phi(N31^5*N52^3-N51^3*N32^5),phi(N31^4*N42^3-N31^4*N42^3));
//	print Degree(Eqc),Degree(Eq2c),Degree(Eq3c),Degree(Gcd([Eqc,Eq2c,Eq3c]));
//	if Degree(Eqc) ne 1 then
//		return "not generic";
//	else
//		print Roots(Eqc);
		c:=Roots(Eqc)[1][1];
		b:=-Evaluate(Derivative(f2,1,z),[1,c])/Evaluate(Derivative(f2,1,x),[1,c]);
		d:=Evaluate(N31,[1,c])*N22*Evaluate(Derivative(f2,1,x)^2,[1,c])/(Evaluate(N21,[1,c])*N32*Evaluate(Derivative(f2,1,x)^3,[1,c]));
//	end if;
	M:=Matrix([[d,b],[c*d,1]]);
	return M2*M*M1;
end function;

P<x,z>:=PolynomialRing(Rationals(),2);
n:=8;
B:=10^1000;
Domain:=[B..2*B];
//Domain:=FF;
// FF<a1,a2,a3,b1,b2,b3,c1,c2,c3>:=FunctionField(Rationals(),9);
//x1:=a1*x^2+a2*x*z+a3*z^2;
//x2:=b1*x^2+b2*x*z+b3*z^2;
//x3:=c1*x^2+c2*x*z+c3*z^2;

F2:=&+[Random(Domain)*x^i*z^(n-i) : i in [0..n]];

//F2:=x^6 + x^4*z^2 + 2*x^3*z^3 + 5*x^2*z^4 + x*z^5 + 7*z^6;
F1:=Evaluate(F2,[Random(Domain)*x+Random(Domain)*z,Random(Domain)*x+Random(Domain)*z]);

time1:=Cputime();
M:=IsGL2GenericEquivalent(F1,F2);
Cputime(time1);
t:=IsDivisibleBy(Evaluate(F2,[M[1,1]*x+M[1,2]*z,M[2,1]*x+M[2,2]*z]),F1);
t;


	P2<u>:=PolynomialRing(Rationals());
	phi:=hom<P-> P2 | 1,u>;
f1:=phi(F1);
f2:=phi(F2);
time2:=Cputime();
IsGL2GeometricEquivalent(f1,f2,n);
Cputime(time2);
