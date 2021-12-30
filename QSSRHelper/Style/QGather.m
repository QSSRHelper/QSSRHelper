(* Wolfram Language package *)

(* Author: ShungHong Li *)





QGather::usage =
"QGather[expr,p,Table\[Rule]True,
	SeparateTransverse\[Rule]True] is a function gather the expr to a more symmetry form about Lorentz structure"







Begin["`Private`QGather`"]




Options[QGather] = {
	Table->True,
	SeparateTransverse->True,
	Subtract->"None",
	SelectD->False}	









QGather[expr_List,p_,rules___Rule]/;And@@(MatchQ[#,{_,_List}]&/@expr):=Plus@@((#[[1]](Plus@@#[[2]]))&/@expr)






QGather[expr:Except[_List],p_,OptionsPattern[]]:=Block[
{tmp,tmp2,tmplor,tmpcoe,tmprem,tmp0,list={},list2,log,llog,null,null1,null0,null2,nulllor,i,n={},l,nn,m,k,ldim,lorentzIndex,tf=OptionValue[Table],separate=OptionValue[SeparateTransverse],subtract=OptionValue[Subtract],nullist,fact,spdfad=False,ord},
tmp=expr//FCI//Expand;

tmp2=Cases[tmp,LorentzIndex[lo_,___]:>lo,Infinity];
If[Length[tmp2]>Length[tmp2//DeleteDuplicates],tmp=tmp//Contract];


If[FreeQ[tmp,Momentum[p,___]],
	tmp
,
	If[OptionValue[SelectD],
		tmp=tmp//Expand;
		tmp=tmp/.{Pair[Momentum[p],LorentzIndex[lo_]]:>Pair[Momentum[p,D],LorentzIndex[lo,D]],Pair[Momentum[p],Momentum[zz_]]:>Pair[Momentum[p,D],Momentum[zz,D]],
					Pair[Momentum[p,D-4],LorentzIndex[lo_,D-4]]->0,Pair[Momentum[p,D-4],Momentum[zz_,D-4]]->0};
		tmp=ChangeDimension[tmp,D]	
	];
	
	
(*		(* FAD[x] \[Rule] 1/SPD[x] *)
	If[!FreeQ[tmp,FeynAmpDenominator],
		spdfad=True;
		tmp=FeynAmpDenominatorSplit[tmp]/.{FeynAmpDenominator[PropagatorDenominator[Momentum[p,di___],mass_]]:>
												1/Pair[Momentum[p,di],Momentum[p,di]],
											FeynAmpDenominator[PropagatorDenominator[aa_ Momentum[p,di___],mass_]]:>
												1/(aa^2 Pair[Momentum[p,di],Momentum[p,di]]),
											FeynAmpDenominator[PropagatorDenominator[ Momentum[bb_ p,di___],mass_]]:>
												1/(bb^2 Pair[Momentum[p,di],Momentum[p,di]]),
											FeynAmpDenominator[PropagatorDenominator[aa_ Momentum[bb_ p,di___],mass_]]:>
												1/((aa bb)^2 Pair[Momentum[p,di],Momentum[p,di]])}
	];
*)	
	
			
	(* check the number of Lorentz index *)
	tmp=tmp//.{Eps[x___,LorentzIndex[lo_,di___],y___]:>null Eps[x,lorentzIndex[lo,di],y],Pair[LorentzIndex[lo_,di___],mom_]:>null Pair[lorentzIndex[lo,di],mom]};

	n=Exponent[tmp,null,List][[1]];
	If[(Length[Exponent[tmp,null,List]]=!=1)&&(n=!=0),Print["Lorentz structure inconsistent! make sure the input is correct."]];
	
	tmp=tmp/.{lorentzIndex->LorentzIndex,null->1};

(*------------------------- refine the log term make it more compact as usuall form -------------------------------*)
	tmp=tmp/.{Log[Power[Pair[Momentum[p,di___],Momentum[p,di___]],po_Integer]]/;Negative[po]:> -Log[Power[Pair[Momentum[p,D],Momentum[p,D]],-po]],
						Log[aa_ Power[Pair[Momentum[p,di___],Momentum[p,di___]],po_Integer]]/;Negative[po]:> -Log[Power[Pair[Momentum[p,D],Momentum[p,D]],-po]/aa]};
						
	(* ----------- isolate the log term if it already show as intended -----------*)					
	tmp=tmp/.{Log[-Pair[Momentum[p,dim___],Momentum[p,dim___]]Power[4Pi ScaleMu^2,-1]]:>llog[-Pair[Momentum[p,dim],Momentum[p,dim]]Power[4Pi ScaleMu^2,-1]],
				Log[-Pair[Momentum[p,dim___],Momentum[p,dim___]]Power[ScaleMu^2,-1]]:>llog[-Pair[Momentum[p,dim],Momentum[p,dim]]Power[ScaleMu^2,-1]]};				
	
											
	tmp=tmp/.Log[x_]/;FreeQ[x,Pair]:>PowerExpand[Log[x]];
	tmp=tmp/.Log[Pair[Momentum[p,dim___],Momentum[p,dim___]]]:>log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(4\[Pi] ScaleMu^2)]+2 Log[2]+Log[Pi]+2 Log[ScaleMu]- Pi I;
	
	tmp=tmp/.Log[a_ Pair[Momentum[p,dim___],Momentum[p,dim___]]]:>log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(4\[Pi] ScaleMu^2)]+2 Log[2]+Log[Pi]+2 Log[ScaleMu]+ PowerExpand[Log[-a]];
	
	tmp=tmp/.Log[a_ Power[Pair[Momentum[p,dim___],Momentum[p,dim___]],-1]]:>-log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(4\[Pi] ScaleMu^2)]-2 Log[2]-Log[Pi]-2 Log[ScaleMu]+ PowerExpand[Log[-a]];


	If[ToLowerCase[ToString[subtract]]=="msbar",
		tmp=tmp/.{log[a_ Pair[Momentum[p,dim___],Momentum[p,dim___]]]:>
						log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(ScaleMu^2)]+2 Log[2]+Log[Pi]+2 Log[ScaleMu]+ PowerExpand[Log[-a]]-EulerGamma,
				log[a_ Power[Pair[Momentum[p,dim___],Momentum[p,dim___]],-1]]:>
						-log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(ScaleMu^2)]-2 Log[2]-Log[Pi]-2 Log[ScaleMu]+ PowerExpand[Log[-a]]+EulerGamma,
				llog[-Pair[Momentum[p,dim___],Momentum[p,dim___]]/(4Pi ScaleMu^2)]:>llog[-Pair[Momentum[p,dim],Momentum[p,dim]]/(ScaleMu^2)]-EulerGamma}
		];

	tmp=tmp/.{llog->log,Log[a_]:>PowerExpand[Log[a]]};
(*--------------------------------------------------------------------------------*)

	(* to separate transverse and longitudinal part,
	first MTD[a,b]-> MTD[a,b] + FVD[p,a]FVD[p,b]/SPD[p], then MTD[a,b]-> MTD[a,b]- FVD[p,a]FVD[p,b]/SPD[p] in the end *)
	(* times a vector so that below can also act on scalar input *)
	tmp=tmp Pair[Momentum[p,D],LorentzIndex[nulllor,D]];
	
	If[separate==True,tmp=tmp/.Pair[LorentzIndex[a_,dim___],LorentzIndex[b_,dim___]]:>
				Pair[LorentzIndex[a,dim],LorentzIndex[b,dim]]+Pair[Momentum[p,dim],LorentzIndex[a,dim]]Pair[Momentum[p,dim],LorentzIndex[b,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]]];

	(* gather to a list *)
	If[n>0,
		tmp=tmp//ExpandAll;

	(* //////// get the terms have same Lorentz structure with first term //////////*)
		While[Head[tmp]===Plus,
			tmpcoe=tmp[[1]]/.{Eps[__]:>1,Pair[LorentzIndex[__],_]:>1};
			tmplor=tmp[[1]]/tmpcoe;
	
			tmprem=tmp/.tmplor:>0;
			tmp0=tmp-tmprem/.{Eps[__]:>1,Pair[LorentzIndex[__],_]:>1};

			tmp=tmprem;
			list=Append[list,{tmplor,tmp0}]
			];

		If[tmp=!=0,
			tmpcoe=tmp/.{Eps[__]:>1,Pair[LorentzIndex[__],_]:>1};
			tmplor=tmp/tmpcoe;
			list=Append[list,{tmplor,tmpcoe}]
			];
	,

		list={{1,tmp}}
	];


(* sorting by power of Epsilon  *)
	ord=Min[Cases[list,Power[Epsilon,pe_]:>pe,Infinity]];
	If[ord<0, ord=-ord , ord=0 ];
	
	For[l=1,l<Length[list]+1,l++,
		list[[l,2]]= CoefficientList[Epsilon^(ord+1)list[[l,2]],Epsilon];
		nn=Length[list[[l,2]]];
		list[[l,2]]=DeleteCases[list[[l,2]]Table[Epsilon^(k-(ord+1)),{k,0,nn-1}],0];
		];


	(* gather longitude part and transverse part*)
	If[separate==True,list=list/.Pair[LorentzIndex[a_,dim___],LorentzIndex[b_,dim___]]:>
				Pair[LorentzIndex[a,dim],LorentzIndex[b,dim]]-Pair[Momentum[p,dim],LorentzIndex[a,dim]]Pair[Momentum[p,dim],LorentzIndex[b,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]]];


	(*----------- subtract Epsilon-pole  ------------*)
	If[((ToLowerCase[ToString[subtract]]=="ms")||(ToLowerCase[ToString[subtract]]=="msbar")) && 
		FreeQ[list//Expand,log[___]Power[Epsilon,_?Negative]]&&FreeQ[list//Expand,Power[log[___],___]Power[Epsilon,_?Negative]],
		list=list/.Power[Epsilon,_?Negative]->0;
		list=list//.{0,b___}:>{b} ];


(*-------------------------Simplify PolyGamma--------------------------------*)
		If[!FreeQ[list,PolyGamma],list=list//FullSimplify];
			(*If[!FreeQ[list,PolyGamma],

			list=list//Expand;
			list=(fact[Cases[#,aa_ PolyGamma[bb_,cc_]|aa_ Power[PolyGamma[bb_,cc_],power_]|PolyGamma[bb_,cc_]|Power[PolyGamma[bb_,cc_],power_]|
								aa_ Zeta[bb_]|aa_ Power[Zeta[bb_],power_]|Zeta[bb_]|Power[Zeta[bb_],power_]]]+(#/.{PolyGamma[___]->0,Zeta[___]->0}))&/@list;
			list=list/.fact[aa_]:>FullSimplify[Plus@@aa+null]/.null->0;
			];*)
	
	
	
	If[tf==True,
	  For[i=1,i<Length[list]+1,i++,
          list[[i,2]]=Simplify[list[[i,2]]]];
      tmp=list,
  
		(* expand to different power of Epsilon; add null1 to isolate Epsilon and other terms to avoid expand them *)
		list=Collect[Epsilon^null0 list,Epsilon]/. a_ Power[Epsilon,b_]:>null1[a//Simplify]Power[Epsilon,b - null0];
		tmp=Total[#]&/@list[[;;,2]];
		tmp=Collect[Total[tmp list[[;;,1]]],Epsilon]/.null0->0;
	
	];
	
	
	(*If[FreeQ[tmp],Log[aa_]/;!FreeQ[aa,Momentum[p,___]]&&spdfad,
		tmp=tmp/.Power[Pair[Momentum[p,dim___],Momentum[p,dim___]],po_Integer]/;Negative[po]\[RuleDelayed]FAD[{p,0-po}]
	];*)
	
	tmp=tmp/.{null1->Identity,log->Log,Pair[Momentum[p,D],LorentzIndex[nulllor,D]]->1};
	
	(* collect the terms only differ by the tensor structure *)
	Flatten[Gather[tmp,(Expand[Plus@@(#1[[2]]+#2[[2]])]===0)||(Expand[Plus@@(#1[[2]]-#2[[2]])]===0)&],1]
	
	
]



]








End[]