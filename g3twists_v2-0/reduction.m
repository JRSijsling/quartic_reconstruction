/*
Routines due to Stoll et al. for minimizing point clusters
apply in order to minimize the (conic, quartic) pair obtained in our algorithms.
*/

///////////////////////////////////////////////////////////////////////////////
// Auxiliary routines

/* Given a zero-dimensional ideal in a multivarible Polynomial Ring and a field.
   This routine returns a list of all Points of this ideal  */

/* The affine case */
GbToPoints := function(gb, tail)
 local up, spez, i, j, rt, f, res;

 if #gb eq 0 then return [tail]; end if;
 up := gb[#gb]; /* This polynomial is univariate */
 suc,up := IsUnivariate(gb[#gb], #gb);
 assert suc;  /* ideal is triangular and zero-dimensional */
 rt := Roots(up);
 res := [];
 for i := 1 to #rt do
  spez := [Evaluate(gb[j], #gb, rt[i][1]) : j in [1..#gb-1]];
  res := res cat $$(spez,[rt[i][1]] cat tail);
 end for;
 return res;
end function;

/* All points defined over nf will be returned */
PointsOfIdeal := function(id, nf)
 local tri, erg, i, gb, up, r_nf;

 erg := [];
 if 1 in id then return erg; end if;

 tri := TriangularDecomposition(Radical(id));
 for i := 1 to #tri do
  gb := GroebnerBasis(tri[i]);
  r_nf := PolynomialRing(nf,Rank(Parent(gb[1])));
  erg := erg cat GbToPoints([r_nf!f : f in gb], []);
 end for;
 return erg;
end function;

/* Computes a vector in the kernel of the floating-point matrix m
   The routine rounds m to a singular matrix.                        */
MyKernelVector := function(m)
 local i,j,k,pz,ps, p_ind, tmp, m1,m2, res;
/* printf "Computing kernel\n"; */
 p_ind := [];
 for i := 1 to Min((#m)-1, #(m[1])) do
/* search for a pivot element */
  pz := i; ps := 1; while ps in p_ind do ps := ps + 1; end while;
  for j := i to #m do
   for k := 1 to #(m[1]) do
    if (not k in p_ind) and (AbsoluteValue(m[j][k]) gt AbsoluteValue(m[pz][ps])) then
     pz := j; ps := k;
    end if;
   end for;
  end for;
  if (AbsoluteValue(m[pz][ps]) gt 0) then
   tmp := m[pz]; m[pz] := m[i]; m[i] := tmp; /* the i-th line is now the pivot-line */
/* We eleminiate the ps column */
   for j := i+1 to #m do
    m1 := m[i][ps]; m2 := m[j][ps];
    tmp := Sqrt(AbsoluteValue(m1)^2 + AbsoluteValue(m2)^2);
    m1 := m1 / tmp; m2 := m2 / tmp;
    for l := 1 to #m[1] do
     tmp := m[i][l];
     m[i][l] := ComplexConjugate(m1) * tmp + ComplexConjugate(m2) * m[j][l];
     m[j][l] := m2 * tmp - m1 * m[j][l];
    end for;
   end for;
   Append(~p_ind,ps);
  end if;
 end for;
 res := [Parent(m[1][1])! 0 : i in [1..#(m[1])]];
 for i := 1 to #m[1] do if not i in p_ind then res[i] := 1; end if; end for;
 if #p_ind eq #m[1] then res[p_ind[#p_ind]] := 1; Remove(~p_ind, #p_ind); end if;

 for i := #p_ind to 1 by -1 do
  tmp := 0;
  for j := 1 to #res do tmp := tmp + res[j] * m[i][j]; end for;
  res[p_ind[i]] := - tmp / m[i][p_ind[i]];
 end for;

 return res;
end function;

ReducePlaneQuartic := function(f)
 local hes,id,i,j,pl, CC, q, mt, subs, res, prec, mul;

 mul := 3;
 prec := Round(100 + 4 * Log(1+Max([AbsoluteValue(i) : i in Coefficients(f)])));
 repeat
  mul := mul^2;
  vprintf PlaneQuartic,1: "Starting reduction using precision %o\n",prec;
  CC := ComplexField(prec);
  hes := Determinant(Matrix([[Derivative(Derivative(f,i),j) : i in [1..3]] : j in [1..3]]));

  id := ideal<PolynomialRing(RationalField(),3) | hes, f, Parent(f).1 - 1 >;
  pl := PointsOfIdeal(id,CC);

  id := ideal<PolynomialRing(RationalField(),3) | hes, f, Parent(f).1, Parent(f).2-1 >;
  pl := pl cat PointsOfIdeal(id,CC);
  id := ideal<PolynomialRing(RationalField(),3) | hes, f, Parent(f).1, Parent(f).2, Parent(f).3-1 >;
  pl := pl cat PointsOfIdeal(id,CC);
  pts := [Vector([ChangePrecision(pl[i][j], prec div 2) : j in [1..3]]) : i in [1..#pl]];
  vprintf PlaneQuartic,1:"Computing covariant\n";
  _,_,Trr := ReduceCluster(pts : eps := 10^(-prec div  20));
/*  Tr := ChangeRing(Tr, RealField(prec));
  Tr := (Tr + Transpose(Tr))/2;
  Trr, U1 := LLLGram(Tr); */
  subs := [&+[Parent(f).i * Trr[i,j] : i in [1..3]] : j in [1..3]];
  res :=  Evaluate(f,subs);

  prec := prec * 2;
 until Max([AbsoluteValue(a) : a in Coefficients(res)]) le mul * Max([AbsoluteValue(a) : a in Coefficients(f)]);

 if Max([AbsoluteValue(a) : a in Coefficients(res)]) ge Max([AbsoluteValue(a) : a in Coefficients(f)]) then
  vprintf PlaneQuartic,1:"Reduction without effect %o\n",res;
  return f,[Parent(f).i : i in [1..3]];
 end if;

 return Evaluate(f,subs),subs;
end function;

ReduceMestreConicAndQuartic := function(f, Q)
 local hes,id,i,j,pl, CC, q, mt, subs, res, prec, mul;

 mul := 3;
 prec := Round(100 + 4 * Log(1+Max([AbsoluteValue(i) : i in Coefficients(f)])));
 repeat
  mul := mul^2;
  vprintf PlaneQuartic,1: "Starting reduction using precision %o\n",prec;
  CC := ComplexField(prec);

  id := ideal<PolynomialRing(RationalField(),3) | Q, f, Parent(f).1 - 1 >;
  pl := PointsOfIdeal(id,CC);
  vprintf PlaneQuartic,1: "Current list of points: %o\n",#pl;

  /* Next two are usually not needed: */
  id := ideal<PolynomialRing(RationalField(),3) | Q, f, Parent(f).1, Parent(f).2-1 >;
  pl := pl cat PointsOfIdeal(id,CC);
  vprintf PlaneQuartic,1: "Current list of points: %o\n",#pl;

  id := ideal<PolynomialRing(RationalField(),3) | Q, f, Parent(f).1, Parent(f).2, Parent(f).3-1 >;
  pl := pl cat PointsOfIdeal(id,CC);
  vprintf PlaneQuartic,1: "Current list of points: %o\n",#pl;

  pts := [Vector([ChangePrecision(pl[i][j], prec div 2) : j in [1..3]]) : i in [1..#pl]];
  vprintf PlaneQuartic,1:"Computing covariant\n";
  ptsnew,_,Trr := ReduceCluster(pts : eps := 10^(-prec div 20));
  //print pts;
  //print ptsnew;
/*  Tr := ChangeRing(Trr, RealField(prec));
  Tr := (Tr + Transpose(Tr))/2;
  Trr, U1 := LLLGram(Tr); */
  subs := [&+[Parent(f).i * Trr[i,j] : i in [1..3]] : j in [1..3]];
  res :=  Evaluate(f,subs);

  prec := prec * 2;
 until Max([AbsoluteValue(a) : a in Coefficients(res)]) le mul * Max([AbsoluteValue(a) : a in Coefficients(f)]);

 if Max([AbsoluteValue(a) : a in Coefficients(res)]) ge Max([AbsoluteValue(a) : a in Coefficients(f)]) then
  vprintf PlaneQuartic,1:"Reduction without effect %o\n",res;
  return f,[Parent(f).i : i in [1..3]];
 end if;

 return Evaluate(f,subs),subs;
end function;
