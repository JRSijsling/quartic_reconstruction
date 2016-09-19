function WPSMinimizeQQ(W, I);

dens := [ Integers() ! Denominator(i) : i in I ];
nums := [ Integers() ! Numerator(i) : i in I ];

gcd_num := GCD(nums);
gcd_den := GCD(dens);
primes := [ fac[1] : fac in Factorization(gcd_den) ] cat [ fac[1] : fac in Factorization(gcd_num) ];
lambda := &*[ p^(Round(Maximum([ Valuation(I[k], p)/W[k] : k in [1..#I] ]))) : p in primes ];

return [ lambda^(-W[k]) * I[k] : k in [1..#I] ], lambda^(-1);

end function;
