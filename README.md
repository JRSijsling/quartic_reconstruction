Description
--

This repository contains Magma code for reconstructing plane quartic curves from their Dixmier--Ohno invariants.

Prerequisites
--

You need to have Magma installed on your machine to use this code. In addition, you can optionally install [`JRSijsling/quartic_isomorphisms`](https://github.com/JRSijsling/quartic_isomorphisms), after which you can uncomment the lines commented out by `Enable if you have quartic_isomorphisms` in `magma/DixmierOhnoToQuartic.m`.

Finally, these algorithms use the Magma algorithm `MinimizeReducePlaneQuartic`, due to Elsenhans and Stoll, to simplify any output over the rationals. In order for this to work properly, one needs a bug fix of the file `magma/package/Geometry/SrfDP/`, which can be found in `BugFix.m`. Alternatively, it is possible to attach this new file separately.

Installation
--

You can enable the functionality of this package in Magma by attaching the `quartic_reconstruction/magma/spec` file with `AttachSpec`. To make this independent of the directory in which you find yourself, and to active this on startup by default, you may want to indicate the relative path in your `~/.magmarc` file, by adding the line
```
AttachSpec("~/Programs/quartic_reconstruction/magma/spec");
```

Usage
--

An example that tests the routines in this package can be found in `Example.m`.

Verbose comments are enabled by
```
SetVerbose("Reconstruction", n);
```
where `n` is either `1` or `2`. A higher value gives more comments.

Credits
--

The papers described the algorithms for minimization and reduction algorithms that are mentioned above and that play a crucial role when using these algorithms over the rationals are:

Andreas-Stephan Elsenhans  
*Good models for cubic surfaces*  
Preprint at [https://math.uni-paderborn.de/fileadmin/mathematik/AG-Computeralgebra/Preprints-elsenhans/red_5.pdf](https://math.uni-paderborn.de/fileadmin/mathematik/AG-Computeralgebra/Preprints-elsenhans/red_5.pdf)

Michael Stoll  
*Reduction theory of point clusters in projective space*  
Groups Geom. Dyn. 5 (2011), no. 2, 553-565  
Preprint at [arXiv:0909.2808](https://arxiv.org/abs/0909.2808)

Citing this code
--

Please cite the following preprint if this code has been helpful in your research:

Reynald Lercier, Christophe Ritzenthaler, and Jeroen Sijsling  
*Reconstructing plane quartic from their invariants*  
Preprint at [arXiv:1606.05594](https://arxiv.org/abs/1606.05594)
