(* Wolfram Language package *)

(* Author: ShungHong Li *)



AGammaD::usage =
	"AGammaD[expr] generate normalized D-dimensional gamma matrices with antisymmetry indices"

AGamma::usage =
	"AGamma[expr] generate normalized gamma matrices with antisymmetry indices"
	
	

Begin["`Private`AGammaD`"]

	
Options[AGammaD] = {
	Dimension->D}


(*-------------------------------------------------------------------------------------------*)


AGammaD[expr___,OptionsPattern[]]:=Block[
{list,tmp,map,sign,resu,dim=OptionValue[Dimension]},
tmp=Level[{expr},{-1}];

list=Table[i,{i,1,Length[tmp]}];
map=Thread[Rule[list,tmp]];

tmp=Permutations[list];
sign=Signature[#]&/@tmp;

If[ToString[dim]=="4",
	1/Length[tmp]Total[sign(GA@@@(tmp/.map))],
	1/Length[tmp]Total[sign(GAD@@@(tmp/.map))]
]
	
]



AGamma[expr___]:=AGammaD[expr,Dimension->4]



End[]