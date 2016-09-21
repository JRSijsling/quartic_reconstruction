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

SetVerbose("Reconstruction", 2);
SetVerbose("G3Twists", 1);
SetVerbose("PlaneQuartic", 1);
SetVerbose("ClusterReduction", 2);

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

//ChangeUniverse(~DOf, F);
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
    // Line for weird bug:
    R<x1, x2, x3> := PolynomialRing(F, 3);
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

/*
A weird example:
Curve before Stoll reduction: 104356924762991471950898*x1^4 -
14885496730651435675480274*x1^3*x2 + 4672890921537997770553850*x1^3*x3 +
795532714999415839432176884*x1^2*x2^2 -
500236424028607042914635872*x1^2*x2*x3 +
78426787961323951359642444*x1^2*x3^2 - 18882097013322292154290455547*x1*x2^3
+ 17832837343560153696794563183*x1*x2^2*x3 -
5601228648845401617724832454*x1*x2*x3^2 +
584679281325586020917967323*x1*x3^3 + 167965660466463977724267510706*x2^4 -
211725718035963650137115752582*x2^3*x3 +
99903030891541957040362756555*x2^2*x3^2 -
20895748929976160285989984525*x2*x3^3 + 1633561421627697775504578339*x3^4
*/
