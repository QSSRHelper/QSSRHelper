(* Wolfram Language package *)

(* Author: ShungHong Li *)




FourierPX2::usage =
"FourierPX2[n,{x,indexlist}] generate inverse Fourier Transformation and it's derivative";


Begin["`Private`FourierPX2`"]

Options[FourierPX2] = {
	TrueGamma->Integer,
	Dimension->D};



(*----------------------------------------------------------------*)
(* the Inverse is samliar, except the overall factor -1/(2\[Pi])^D, 
and replace every -i\[PartialD] \[Rule] i\[PartialD] which can be absorbed in overall sign*)

FourierPX2[m_,v_,OptionsPattern[]]:=Block[{opt=OptionValue[TrueGamma],l,dim=OptionValue[Dimension]},

l=If[Length[v]==0,1,Length[v]];

(-1)^l/(2Pi)^(4-2Epsilon)FourierXP2[m,v,TrueGamma->opt,Dimension->dim]]


End[]