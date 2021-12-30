# QSSRHelper
A mathematica package for QCD Sum Rules calculation.

# Requirements
The QSSRHelper require [FeynCalc](https://feyncalc.github.io/) 9.3.0+ and Mathematica 12.0+.

# installation
To install this package, put the folder `QSSRHelper` in the `$UserBaseDirectory` of Mathematica, e.g. `C:\Users\usrname\AppData\Roaming\Mathematica\Applications` for Windows and `/home/username/.Mathmatica/Applicatons` for Ubuntu.

# usage
Load FeynCalc before load QSSRHelper (the [TARCER](https://arxiv.org/pdf/hep-ph/9801383.pdf) is needed):
```
Global`$LoadAddOns = {"TARCER"};
<< FeynCalc`
<<QSSRHelper`
```
For basic usuage and simple example, search "QSSRHelper" in Help Center of Mathematica.

# license
This software is covered by the GNU General Public License 3.

Copyright (C) 2021 ShuangHong Li

# Notice
The construction of this package is far from complete, but it already has been used in [arXiv:2111.13897](https://arxiv.org/abs/2111.13897), so I put it here.

