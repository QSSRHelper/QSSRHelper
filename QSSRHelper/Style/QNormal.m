

(* Wolfram Language package *)

(* Author: ShungHong Li *)


QNormal::usage = "QNormal[expr] refine the expr by Replace qfact1->Identity,qfact2->Identity,qGamma->Gamma;
 if qdelta involved, take the limit qdelta->0 by default.";


Begin["`Private`QNormal`"]
Options[QNormal]={Limit->True}

QNormal[expr_,OptionsPattern[]]:=If[ToLowerCase[ToString[OptionValue[Limit]]]==="false",
	expr/.{qfact1->Identity,qfact2->Identity,qGamma->Gamma}
,
	Limit[expr/.{qfact1->Identity,qfact2->Identity,qGamma->Gamma},qdelta->0]
]



End[]