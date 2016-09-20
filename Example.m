/***
 *  Generating random examples of reconstruction
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
 *  Copyright 2016 R. Lercier, C. Ritzenthaler & J. Sijsling
 */

AttachSpec("package/spec");
AttachSpec("g3twists_v2-0/spec");

SetVerbose("G3Twists", 1);
SetVerbose("Reconstruction", 2);

/* Start from a random ternary quartic */
F := Rationals();  B := 2^6; Domain := [-B..B];
//F := GF(NextPrime(10^5));  Domain := F;
R<x1, x2, x3> := PolynomialRing(F, 3);
repeat
    f := &+[ Random(Domain)*mon : mon in MonomialsOfDegree(R, 4) ];
    DOf, DOWght := DixmierOhnoInvariants(f);
until DOf[#DOf] ne 0;

print "";
print "Start from f =", f;

DOf :=
[ 736, 31736/9, 5478349480/9, 370812440, 5848756668800/81, 463806801920,
27749480601500000/243, 235318365253600/9, 29880174142240888000/243,
1237392066266302400/27, 2622131250028599100160/81, 4661056001494589562880/9,
11081735239253131872 ]
;
//DOf :=
//[ 15340133, -299059435806715/36, 871066033804668174452045/36, 31974951430657691732195/4, 71835838196322664987016141672123/324, 7518988863248702193646167261259/12,
//-16869518852139975000172343280302345327057/3888, -271320673764862458916544085288090684133/144, 418290119858604793158859161422895598717950748969/3888,
//-16022594179441615908539426925365461910408719471/432, 136322308455775615401495398705274701923844848810036783/324, 1223619074049295502791923821057051891106418814228049929/144,
//744195685151654201468081876247448017552114221938275349893850595328 ]
//;

ChangeUniverse(~DOf, F);
DOf_norm := WPSNormalize(DOWght, DOf);
print "";
print "Its invariants are", DOf;
print "";
print "Its normalized invariants are", DOf_norm;

/* Construct another quartic with equivalent invariants */
g, aut := TernaryQuarticFromDixmierOhnoInvariants(DOf : exact := false);
g := R ! g;
print "Automorphism group", aut;
if F eq Rationals() then
    print g;
    print "Model over QQ found. Reducing its coefficients...";
    g := R ! MinimizeReducePlaneQuartic(g);
end if;
print "";
print "The reconstructed curve is g =", g;

/* Compute its invariants normalize */
DOg, _ := DixmierOhnoInvariants(g);
ChangeUniverse(~DOg, F);
DOg_norm := WPSNormalize(DOWght, DOg);
//print "";
//print "Its invariants are", DOg;
//print "";
//print "Its normalized invariants are", DOg_norm;

/* Check everything's fine */
print "";
print "Test for equality of actual invariants:", DOf eq DOg;
print "";
print "Test for equality of normalized invariants:", DOf_norm eq DOg_norm;

exit;
