(* Wolfram Language package *)

(* Author: ShungHong Li *)




QEvaluate::usage = 
"QEvaluate[expr,p,Order->0] expand expr to \[Epsilon]-Series, for large input expr, QEvaluate automatically use Parallelize evaluation "



Begin["`Private`QEvaluate`"]




Options[QEvaluate] = {
	D->4-2Epsilon,
	Order->0,
	OnebyOne->False,
	Subtract->"None",
	Parallelize->"Auto"}




QEvaluate[expr_,p_,symm_List:{0},OptionsPattern[]]:=Block[
{tmp,tmp2,null,null1,null2,list,list2,nullist,tmplist,log,plus,nlocal=True,ieps,ilog,dimm=OptionValue[D],ord=OptionValue[Order],parall=OptionValue[Parallelize],i,j},

tmp=expr//FCI//QSimplify2;

tmp2=Cases[tmp,LorentzIndex[lo_,___]:>lo,Infinity];
If[Length[tmp2]>Length[tmp2//DeleteDuplicates],tmp=tmp//QContract];(* Contract if have dummy indices *)

If[symm=!={0},tmp=QSymmetry[tmp,symm]];

If[FreeQ[tmp,Momentum[p,___]],
	tmp
,
		
	(* FAD[x] \[Rule] 1/SPD[x] *)
	If[!FreeQ[tmp,FeynAmpDenominator],
		tmp=FeynAmpDenominatorSplit[tmp]/.{FeynAmpDenominator[PropagatorDenominator[Momentum[p,di___],mass_]]:>
												1/Pair[Momentum[p,di],Momentum[p,di]],
											FeynAmpDenominator[PropagatorDenominator[aa_ Momentum[p,di___],mass_]]:>
												1/(aa^2 Pair[Momentum[p,di],Momentum[p,di]]),
											FeynAmpDenominator[PropagatorDenominator[ Momentum[bb_ p,di___],mass_]]:>
												1/(bb^2 Pair[Momentum[p,di],Momentum[p,di]]),
											FeynAmpDenominator[PropagatorDenominator[aa_ Momentum[bb_ p,di___],mass_]]:>
												1/((aa bb)^2 Pair[Momentum[p,di],Momentum[p,di]])}
	];
	
	
	
	tmp=Expand[tmp];
	tmp=tmp/.{Pair[Momentum[p],LorentzIndex[lo_]]:>Pair[Momentum[p,D],LorentzIndex[lo,D]],Pair[Momentum[p],Momentum[zz_]]:>Pair[Momentum[p,D],Momentum[zz,D]],
				Pair[Momentum[p,D-4],LorentzIndex[lo_,D-4]]->0,Pair[Momentum[p,D-4],Momentum[zz_,D-4]]->0,Pair[LorentzIndex[_,D-4],LorentzIndex[_,D-4]]->0};
				
	tmp=ChangeDimension[tmp,D];
	tmp=QDimension[tmp,D->dimm];
	tmp2=Cases[tmp,Epsilon,Infinity];
	
	(*------------------------------------------------------------*)
	If[FreeQ[tmp,Epsilon],

		tmp=QGather[tmp,p,Table->False]
	,
		
		(*-------weather or not use parallelize evaluation--------*)
		If[((Length[tmp2]>500)&&(ToString[Head[tmp]]=="Plus")&&(ToLowerCase[ToString[parall]]=="auto"))||(ToLowerCase[ToString[parall]]=="true"),
		
			tmp=tmp/.{qGamma->Gamma,qfact1->Identity};
			tmp=tmp//Expand;
			tmp=tmp+null+null^2;
			
			
			(* ----------here is a strange, when ParallelMap[Series[]...] write in package, the 'ord' in ParallelMap[Series[#,{Epsilon,0,ord}]&,tmp] will be treat as a symbol,
			seems mahtematica distribuate 'Series[#,{Epsilon,0,ord}]&' before assign the value of ord to 'ord'. althougth it works well when write in notebook-------- *)
			
			(* some times there's warning "Unable to decide whether numeric quantity ... is equal to zero. Assuming it is. " expand tmp can prevent it but cause time consuming  *)
			If[OptionValue[OnebyOne]===True,
				tmp={ord,#}&/@(List@@Expand[tmp/.qfact2->Identity])
			,
				tmp=({ord,#}&/@(List@@tmp))/.qfact2->Identity;			
			];
			
			
			tmp=ParallelMap[Series[#[[2]],{Epsilon,0,#[[1]]}]&,tmp]//Total//Normal;
			tmp=(tmp//Expand)/.null->0;
			
			
			tmp=QGather[tmp,p,Subtract->OptionValue[Subtract],SelectD->True,Table->"ForcetoTable"];
			
		(*  MTD[a,b]\[Rule] MTD[a,b] + FVD[p,a]FVD[p,b]/SPD[p], then MTD[a,b]\[Rule] MTD[a,b]- FVD[p,a]FVD[p,b]/SPD[p] in the end *)
			tmp=tmp/.Pair[LorentzIndex[x_,dim___],LorentzIndex[y_,dim___]]:>
					 null1[x,y] Pair[LorentzIndex[x,dim],LorentzIndex[y,dim]]+Pair[Momentum[p,dim],LorentzIndex[x,dim]]Pair[Momentum[p,dim],LorentzIndex[y,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]];

			(*-------- sort by Epsilon & Lorentz structure --------*)
			tmp=tmp Epsilon^(-(ord+1));
			tmp=(Total[#[[1]]#[[2]]]&/@tmp)//Total;
			tmp=Collect[tmp,Epsilon];
			
			
			If[ToString[Head[tmp]]=="Plus",
				tmp=Epsilon^(2(ord+1))(List@@tmp);
				tmp=Collect[#,null1[___]]&/@tmp;
				
				tmp=If[ToString[Head[#]]=="Plus",Simplify[List@@#]//Total,#]&/@tmp;
				tmp=tmp//Total;
			,
				tmp=Epsilon^(2(ord+1))tmp;
				tmp=Collect[tmp,null1[___]];
				
				If[ToString[Head[tmp]]=="Plus",tmp=Simplify[List@@tmp]//Total]
			];
			
			
			
			tmp=tmp/.{Pair[LorentzIndex[x_,dim___],LorentzIndex[y_,dim___]]:>
					Pair[LorentzIndex[x,dim],LorentzIndex[y,dim]]-Pair[Momentum[p,dim],LorentzIndex[x,dim]]Pair[Momentum[p,dim],LorentzIndex[y,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]],null1[___]->1}
			
							
		,
			QEvaluate2[tmp,p,Order->OptionValue[Order],D->dimm,Subtract->OptionValue[Subtract],OnebyOne->OptionValue[OnebyOne]]
			
		]		
	]

]
]














End[]