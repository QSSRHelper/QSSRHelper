(* Wolfram Language package *)

(* Author: ShungHong Li *)




FourierPX::usage =
"FourierPX[expr,{p,x}] id D-dimensional Fourier Transformation from
momentum space {p} to coordinate space {x}. 
It's equivalant to set Option Inverse->True in FourierXP";




Begin["`Private`FourierPX`"]


Options[FourierPX]={
	TrueGamma->Integer,
	Dimension->"AsIs",
	Simplify->True,
	Parallelize->"Auto"};
	
	
	
	
FourierPX[expr_,{x_,p_},OptionsPattern[]]:=Block[{option=OptionValue[TrueGamma],dim=OptionValue[Dimension]},

	FourierXP[expr,{x,p},TrueGamma->option,Dimension->dim,Inverse->True,Simplify->OptionValue[Simplify]]
]
	
	

End[]