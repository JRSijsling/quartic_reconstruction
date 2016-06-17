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
SetVerbose("Reconstruction", 2);

/* Start from a random ternary quartic */
//F := Rationals();  B := 1; Domain := [-B..B];
F := GF(NextPrime(10^5));  Domain := F;
R<x1, x2, x3> := PolynomialRing(F, 3);
f := &+[ Random(Domain)*mon : mon in MonomialsOfDegree(R, 4) ];

print "";
print "Start from f =", f;

/* Compute its invariants normalize */
DOf, DOWght := DixmierOhnoInvariants(f);
ChangeUniverse(~DOf, F);
DOf_norm := WPSNormalize(DOWght, DOf);
print "";
print "Its invariants are", DOf_norm;
print "";
print "Its normalized invariants are", DOf_norm;

/* Construct another quartic with equivalent invariants */
//g := TernaryQuarticFromDixmierOhnoInvariant(DOf);
g := TernaryQuarticFromDixmierOhnoInvariants(DOf : exact := true);
print "";
print "The reconstructed curve is g =", g;

/* Compute its invariants normalize */
DOg, _ := DixmierOhnoInvariants(g);
ChangeUniverse(~DOg, F);
DOg_norm := WPSNormalize(DOWght, DOg);
print "";
print "Its invariants are", DOg_norm;
print "";
print "Its normalized invariants are", DOg_norm;

/* Check everything's fine */
print "";
print "Test for equality of actual invariants:", DOf eq DOg;
print "";
print "Test for equality of normalized invariants:", DOf_norm eq DOg_norm;

exit;
