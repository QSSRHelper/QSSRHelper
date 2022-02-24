(* Wolfram Language package *)

(* Author: ShungHong Li *)




FourierXP2::usage =
"FourierXP2[n,{p,indexlist}] generate Fourier Transformation and it's derivative";


Begin["`Private`FourierXP2`"]



Options[FourierXP2] = {
	TrueGamma->Integer,
	Dimension->D};



FourierXP2[m_,v_,OptionsPattern[]]:=Block[
{i,j,n,temp,co,result,p,l,opt=OptionValue[TrueGamma],dim=OptionValue[Dimension],dims,null},

l=Length[v];
If[l>1,p=v[[1]],p=v];
(* v = {p, \[Mu],\[Nu],...}. the \[Mu],\[Nu]... represent partial differentiate: -i\[PartialD]/\[PartialD]p^\[Mu] -i\[PartialD]/\[PartialD]p^\[Nu]...*)
If[dim==4,dims=4,dims=D];

n=m/.\[Epsilon]->Epsilon;(* allow writte Epsilon as \[Epsilon] for convenient *)

co=-I (-1)^n 2^(dim-2n) Pi^(dim/2) qGamma[dim/2 - n]/qGamma[n];(*coefficient*)

temp=(-Pair[Momentum[p,dims],Momentum[p,dims]])^null[-dim/2+n];

If[l>0,

	For[j=1, j<l, j++,
	temp = -I FourDivergence[temp, Pair[LorentzIndex[v[[-j]],dims],Momentum[p,dims]]];
	temp =temp/.{Times[null[xx_]+yy_,zz_]-> -zz qGamma[-xx-yy+1]/qGamma[-xx-yy],Times[null[xx_],zz_]-> -zz qGamma[-xx +1]/qGamma[-xx]}]
];(*derivative if need;incorporate qGamma[] with the factor generated by derivative *)

result=co temp/.null[x_]->x//Simplify;


If[opt==Integer, result=result/.qGamma[nn_Integer]:>Gamma[nn]];

If[opt==All,result=result/.qGamma:>qGamma2];

result
]


End[]


