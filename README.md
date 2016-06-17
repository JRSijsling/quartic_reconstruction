Description
-----------

This repository contains Magma code for reconstructing plane quartic curves
from their Dixmier-Ohno invariants.

Installation
------------

A copy of the computer algebra system Magma is needed to run this code. After being cloned or downloaded, it can be made to run upon startup of Magma by adding the line

AttachSpec("[PATH]/package/spec");

to the user's .magmarc file, which can typically be found in the home directory). Here [PATH] is to be replaced by the directory of the cloned and downloaded repository, so that one could for example have

AttachSpec("~/Programs/Reconstruction/package/spec");

Usage
-----

An example that tests the routines in this package can be found in Example.m. As in that file, more verbose comments during the your run can be enable by

SetVerbose("Reconstruction", n);

where n is either 1 or 2. A higher value gives more comments.

When reconstructing over the rationals, you may want to run Michael Stoll's MinimizeReducePlaneQuartic function on the output.

Citing this code
----------------

If you have used this code and it has been helpful, then please consider citing the corresponding preprint:

Reynald Lercier, Christophe Ritzenthaler, and Jeroen Sijsling  
*Reconstructing plane quartic from their invariants*  
[ArXiV link upcoming.]
