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

SetVerbose("Reconstruction", 1);
SetVerbose("G3Twists", 1);
SetVerbose("PlaneQuartic", 1);
SetVerbose("Descent", 1);
//SetVerbose("ClusterReduction", 2);

/* Start from a random ternary quartic */
F := Rationals();  B := 2^7; Domain := [-B..B];
//F := GF(NextPrime(10^5));  Domain := F;
R<x1, x2, x3> := PolynomialRing(F, 3);
repeat
    f := &+[ Random(Domain)*mon : mon in MonomialsOfDegree(R, 4) ];
    DOf, DOWght := DixmierOhnoInvariants(f);
until DOf[#DOf] ne 0;

//DOf :=
//[ 164740788317057490760423648, -19180827794452733902906485333544636922103819683\
//9544, 1068409046848112548257540924456416489890950027443272843839371568268338534\
//036200, -8380116349780711412446371021544639096082980069184622999361824163319010\
//66122600, -61311986757821920576933476996214070924040125060196214687610703257404\
//17590817985247595776801426064112000, 133845954514437992082107655483318843801956\
//97245844903979278162460422932132884370894053259199537231161600, 
//2656541012532325022771309038641843363104236829679447434819842609585879996707814\
//647829536497449729101508450194759386245981667908000, 
//-139562186590004582944153999558359381667128918577467543564073076707592813309231\
//2529587047853732579546014091863946860625444848836000, 
//3207060839397255929190895708797524886782174194814389207728133840953398340596138\
//45468374270978356797347519700765797627337959913846972922834328914377796200000, 
//-858020463678759357262848530063912674793740126378698672081810230661402152549702\
//85402660137903937343114019088959380393410857578191428634311215658090086200000, 
//1223707767713403572972977693506517606889382793011335605383119139726997497414229\
//7051740945087535671920137787381601412056041605035315453055778171135520991480347\
//79686844741174417696000, 173037519943050021621220568575325063451231384056155226\
//6264746154925764066397301975713799485012682861579704040851088662993607235818844\
//5827989240065662965876683583406379516224540800000, 
//4235064801221358196098083217959438169529754046975305206234264088832863515428583\
//4587212493715631064105134418955972665466241086381462514268138177516700859345385\
//096577684100947475546728313517584032072451120635674371295035414101692878176 ]
//;

print "";
print "Start from f =", f;

DOf_norm := WPSNormalize(DOWght, DOf);
print "";
print "Its invariants are", DOf;

/* Construct another quartic with equivalent invariants */
g, aut, twists, bp0 := TernaryQuarticFromDixmierOhnoInvariants(DOf : Exact := false);
g := R ! g;
if F eq Rationals() then
    vprint Reconstruction : "A first model over the rationals is given by";
    print g;
    print "Automorphism group", aut;
    print "Reducing coefficients...";
    R<x1, x2, x3> := PolynomialRing(F, 3);
    g := R ! MinimizeReducePlaneQuartic(g : bp0 := bp0);
end if;
print "";
print "The reconstructed curve is g =", g;

/* Compute its invariants and normalize */
DOg, _ := DixmierOhnoInvariants(g);
ChangeUniverse(~DOg, F);
DOg_norm := WPSNormalize(DOWght, DOg);

/* Check everything's fine */
print "";
print "Test for equality of actual invariants:", DOf eq DOg;
print "";
print "Test for equality of normalized invariants:", DOf_norm eq DOg_norm;

exit;
