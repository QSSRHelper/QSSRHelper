(* ::Package:: *)

(* Wolfram Language package *)

(* Author: ShungHong Li *)






QSimplify::usage= "QSimplify[expr_] is a specific Simplify function that simplify the dummy indices and Gamma functions";






Begin["`Private`QSimplify`"]


Options[QSimplify] = {
	NonCommutative->{},
	Contract->False,
	Lorentz->"Auto",
	Color->"Auto",
	Symmetry->"None",
	Separate->{"null"}}
(*---------------------------------------------------------------*)

QSimplify[expr_,OptionsPattern[]]:=IndexSimplify[expr,
	QSimplify2->True,
	NonCommutative->OptionValue[NonCommutative],
	Contract->OptionValue[Contract],
	Lorentz->OptionValue[Lorentz],
	Color->OptionValue[Color],
	Symmetry->OptionValue[Symmetry],
	QSimplify2Rules->OptionValue[Separate]]/.qfact2[aa_]:>qfact2[aa//Simplify]
	



End[]
