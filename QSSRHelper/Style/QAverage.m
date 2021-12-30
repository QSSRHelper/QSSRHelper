(* Wolfram Language package *)

(* Author: ShungHong Li *)




QAverage::usage = 
	"QAverage[expr,p] is a function which average momentum vectors to scalar product with metrices tensor"
	

Begin["`Private`QAverage`"]





QAverage[expr_,p_]:=Block[{tmp,tmp2,tmp0,ap,list,null,null2,null0,l0,l1,i,j,l,n,k,m,tmpg,tmplist,times,plus},
tmp=expr//FCI;
tmp=tmp/.Momentum[xx_,dim___]/;!FreeQ[xx,p]:>Momentum[Expand[xx],dim];

tmp=tmp//.{Pair[Momentum[p+y_,dim___],LorentzIndex[index_,dim___]]:>Pair[Momentum[p,dim],LorentzIndex[index,dim]]+ Pair[Momentum[y,dim],LorentzIndex[index,dim]],
			Pair[Momentum[x_ p+y_,dim___],LorentzIndex[index_,dim___]]:>x Pair[Momentum[p,dim],LorentzIndex[index,dim]]+ Pair[Momentum[y,dim],LorentzIndex[index,dim]]};

If[!FreeQ[tmp,Momentum[p,___]],

	If[!FreeQ[tmp,DiracGamma]||!FreeQ[tmp,Eps],tmp=Uncontract[DiracGammaExpand[tmp],p]];
(* uncontract if GSD[p] involved *)

	tmp=tmp//.Pair[Momentum[p,___],LorentzIndex[index_,___]]:>null null2[index];

	tmp=tmp null^2;(* seprate terms no FVD[p,mu] involved *)
	tmp0=Collect[tmp,null]/.Power[null,a_]/;a>2 ->0;
	tmp=tmp-tmp0;

	tmp=Collect[null^2 tmp,null2[_]]/.Power[null,_?OddQ]->0;


	tmp=((tmp+null0 null2[l0]null2[l1])//Expand)/.Plus->plus;
	tmp=tmp/.Power[null2[x_],mm_]:>Apply[times,Table[null2[x],{k,mm}]];

	For[i=1,i<Length[tmp]+1,i++,
		list={};
		tmp2=tmp[[i]];
		tmp2//.null2[a_]:>(list=Append[list,a];1);
		m=Length[list]/2;

		list=list//.List[ll1_,ll___]:>(l=1;tmpg=0;tmplist=List[ll];
						n=Length[tmplist]+1;
	
						For[l=1,l<Length[tmplist]+1,l++,
							tmpg=tmpg+times[MTD[ll1,tmplist[[1]]],tmplist[[2;;]]];
							tmplist=RotateLeft[tmplist]];
						tmpg);

		tmp[[i]]=tmp[[i]] SPD[p]^m Product[1/(D+2k),{k,0,m-1}] list/.{}->1

	];	

	tmp=tmp0 + tmp/.{times->Times,plus->Plus,null2[_]->1,null->1,null0->0}
];

tmp

]





QAverage[expr_,p_,vectors_List]:=Block[{tmp,m,vector},
tmp=QAverage[expr,p]/.Momentum[xx_,dim___]:>Momentum[Expand[xx],dim];

For[m=1,m<Length[vectors]+1,m++,
	vector=vectors[[m]];
	tmp=tmp//.{Pair[Momentum[vector a_+y_,dd_],LorentzIndex[i_,dd_]]:> a Pair[Momentum[vector,dd],LorentzIndex[i,dd]]+Pair[Momentum[y,dd],LorentzIndex[i,dd]],
			Pair[Momentum[vector +y_,dd_],LorentzIndex[i_,dd_]]:> Pair[Momentum[vector,dd],LorentzIndex[i,dd]]+Pair[Momentum[y,dd],LorentzIndex[i,dd]],
			Pair[Momentum[vector a_,dd_],LorentzIndex[i_,dd_]]:> a Pair[Momentum[vector,dd],LorentzIndex[i,dd]]}];
	
tmp
]






End[]