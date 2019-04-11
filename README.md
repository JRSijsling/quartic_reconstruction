Description
-----------

This repository contains Magma code for reconstructing plane quartic curves
from their Dixmier-Ohno invariants.

Installation
------------

A copy of the computer algebra system Magma is needed to run this code. After being cloned or downloaded, it can be made to run upon startup of Magma by adding the lines

AttachSpec("[PATH]/package/spec");  
AttachSpec("[PATH]/g3twists\_v2-0/spec");

to the user's .magmarc file, which can typically be found in the home directory). Here [PATH] is to be replaced by the directory of the cloned and downloaded repository, so that one could for example have

AttachSpec("\~/Programs/Reconstruction/package/spec");  
AttachSpec("\~/Programs/Reconstruction/g3twists\_v2-0/spec");

A bug fix
---------

The functionality also uses the Magma algorithm MinimizeReducePlaneQuartic, due to Elsenhans and Stoll, to simplify any output over the rationals. In order for this to work properly, one needs a bug fix of the file magma/package/Geometry/SrfDP/, which can be found in BugFix.m.

The papers in which the methods used in this fundamental algorithm are described are:

Andreas-Stephan Elsenhans  
*Good models for cubic surfaces*  
Preprint at [https://math.uni-paderborn.de/fileadmin/mathematik/AG-Computeralgebra/Preprints-elsenhans/red_5.pdf](https://math.uni-paderborn.de/fileadmin/mathematik/AG-Computeralgebra/Preprints-elsenhans/red_5.pdf "https://math.uni-paderborn.de/fileadmin/mathematik/AG-Computeralgebra/Preprints-elsenhans/red_5.pdf")

Michael Stoll  
*Reduction theory of point clusters in projective space*  
Groups Geom. Dyn. 5 (2011), no. 2, 553-565  
Preprint at [http://arxiv.org/abs/0909.2808](http://arxiv.org/abs/0909.2808 "http://arxiv.org/abs/0909.2808")

Usage
-----

An example that tests the routines in this package can be found in Example.m. As in that file, more verbose comments during the your run can be enabled by

SetVerbose("Reconstruction", n);

where n is either 1 or 2. A higher value gives more comments.

Citing this code
----------------

If you have used this code and it has been helpful, then please consider citing the corresponding preprint:

Reynald Lercier, Christophe Ritzenthaler, and Jeroen Sijsling  
*Reconstructing plane quartic from their invariants*  
Preprint at [http://arxiv.org/abs/1606.05594](http://arxiv.org/abs/1606.05594 "http://arxiv.org/abs/1606.05594")
