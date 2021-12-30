(* Wolfram Language package *)

QDimension::usage = 
"QDimension[expr,dim] set dimension D -> dim in power and qGamma";


Begin["`Private`QDimension`"]

Options[QDimension]={
	D->4-2Epsilon};


(*QDimension[expr_,dim_,level_]:=Block[{temp},
temp=FCReplaceD[expr,D\[Rule]dim];
temp=Replace[temp,{qGamma[x_]:>qGamma[x/.D->dim],Power[a_,b_]:>Power[a,b/.D->dim]},{0,level}]
];*)

QDimension[expr_,OptionsPattern[]]:=Block[{tmp,dim=OptionValue[D],tmpdim},
	
tmp=expr//FCI;	

(* protect the D in FAD,SPD,FVD,GAD *)
tmp=tmp/.{Momentum[xx_,dimm___]:>Momentum[xx,tmpdim[ToString[dimm]]],LorentzIndex[lor_,dimm___]:>LorentzIndex[lor,tmpdim[ToString[dimm]]]}/.
			DiracGamma[gg_,dimm___]:>DiracGamma[gg,tmpdim[ToString[dimm]]];

(* replace D -> dim; Expand make the Epsilon in these terms looks more clear *)
tmp=(tmp/.{qGamma[x_]:>qGamma[Expand[x/.D->dim]],Gamma[x_]:>Gamma[Expand[x/.D->dim]]})/.Power[a_,b_]:>Power[a,Expand[b/.D->dim]]/.D->dim;

tmp=tmp/.tmpdim[dimm_]:>ToExpression[dimm]
];



End[]