(* ::Package:: *)

(* Wolfram Language package *)

(* Author: ShungHong Li *)






QEvaluate2::usage = 
"QEvaluate2[expr,p,Order->0]expand expr to \[Epsilon]-Series "





Begin["`Private`QEvaluate2`"]


Options[QEvaluate2]={
	D->4-2Epsilon,
	Order->0,
	OnebyOne->False,
	Subtract->"None"}







(*
tmp=(g^(-5+(3*D)/2)*((-38313*2^(2-2*D))/Pi^D+(3969*2^(4-2*D))/(D*Pi^D)+(160245*D)/(2^(2*D)*Pi^D)-(381795*2^(-2-2*D)*D^2)/Pi^D
		+(286083*2^(-3-2*D)*D^3)/Pi^D-(17511*2^(-1-2*D)*D^4)/Pi^D+(5613*2^(-2-2*D)*D^5)/Pi^D-(9099*2^(-6-2*D)*D^6)/Pi^D+(1059*2^(-7-2*D)*D^7)/Pi^D
		-(27*2^(-7-2*D)*D^8)/Pi^D)*Gamma[5-(3*D)/2]*Gamma[2-D/2]*Gamma[-3+D/2]^3)/(Pi^(D/2)*Gamma[-4+2*D])
		
			
		tmp=tmp/.D\[Rule]4-2\[Epsilon];
		tmp2=tmp//Expand;
		
		(* It is strange that Series[tmp2] =/= Series[tmp] *)
		
		Print["1---------> ",Simplify[Series[tmp2,{\[Epsilon],0,0}]- Series[tmp,{\[Epsilon],0,0}]]];

		(* However, Series[] for each term of tmp2 = Series[tmp] *)
		Print["2---------> ",Simplify[Series[#,{\[Epsilon],0,0}]&/@tmp2-Series[tmp,{\[Epsilon],0,0}]]];

*)

QEvaluate2[expr_,p_,symm_List:{0},OptionsPattern[]]:=Block[
{tmp,tmp2,null0,null,null1,null2,list,list2,nullist,tmplist,log,plus,nlocal=True,ieps,ilog,dimm=OptionValue[D],ldim=4,ldim2=4,ord=OptionValue[Order],i,j,subtract=OptionValue[Subtract],fact},

tmp=expr//FCI;

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
	
	
	tmp=Expand[tmp//QContract];
	(* discard dimension D-4 terms, write all terms as dimension D to make it looks more clearly *)
	tmp=tmp/.{Pair[Momentum[p],LorentzIndex[lo_]]:>Pair[Momentum[p,D],LorentzIndex[lo,D]],Pair[Momentum[p],Momentum[zz_]]:>Pair[Momentum[p,D],Momentum[zz,D]],
				Pair[Momentum[p,D-4],LorentzIndex[lo_,D-4]]->0,Pair[Momentum[p,D-4],Momentum[zz_,D-4]]->0,Pair[LorentzIndex[_,D-4],LorentzIndex[_,D-4]]->0};
			
	If[symm=!={0},tmp=QSymmetry[tmp,symm]];			
				
	tmp=ChangeDimension[tmp,D];
	tmp=QDimension[tmp,D->dimm];(*see QDimension*)


	If[FreeQ[tmp,Epsilon],

		tmp=QGather[tmp,p]
	,
			
		tmp=tmp/.{qGamma->Gamma,qfact1->Identity,qfact2->Identity};
		tmp=tmp+null2+null2^2;
		
	(*   Do not Expand[tmp] before Series[]! It's quit strange that Expand tmp before evaluate Series will cause problem some time, 
		e.g. antisymmetrize expr before apply this function, if Expand[] the expression before Series[], the symmetry part will appear in some case.
		there's no problem if eveluate one term every time, or not Expand[] before Series[].
		
			to see this strange, try uncomment below three line reload the package and run :
		tmp=(g^(-5+(3*D)/2)*((-38313*2^(2-2*D))/Pi^D+(3969*2^(4-2*D))/(D*Pi^D)+(160245*D)/(2^(2*D)*Pi^D)-(381795*2^(-2-2*D)*D^2)/Pi^D
		+(286083*2^(-3-2*D)*D^3)/Pi^D-(17511*2^(-1-2*D)*D^4)/Pi^D+(5613*2^(-2-2*D)*D^5)/Pi^D-(9099*2^(-6-2*D)*D^6)/Pi^D+(1059*2^(-7-2*D)*D^7)/Pi^D
		-(27*2^(-7-2*D)*D^8)/Pi^D)*f[\[Rho]]*f[\[Eta],\[Mu]]*Gamma[5-(3*D)/2]*Gamma[2-D/2]*Gamma[-3+D/2]^3)/(Pi^(D/2)*Gamma[-4+2*D])
		
		tmp=tmp-(tmp/.{\[Rho]\[Rule]\[Eta],\[Eta]\[Rule]\[Rho]});		
		tmp=tmp/.D\[Rule]4-2\[Epsilon];
		tmp2=tmp//Expand;
		Print["1---------> ",(tmp2+(tmp2/.{\[Rho]\[Rule]\[Eta],\[Eta]\[Rule]\[Rho]}))//Simplify];
		tmp2=Series[tmp2,{\[Epsilon],0,0}]//Expand;
		Print["2---------> ",(tmp2+(tmp2/.{\[Rho]\[Rule]\[Eta],\[Eta]\[Rule]\[Rho]}))//Normal//Simplify];

		Print["1---------> ",(tmp+(tmp/.{\[Rho]\[Rule]\[Eta],\[Eta]\[Rule]\[Rho]}))//Simplify];
		tmp=Series[tmp,{\[Epsilon],0,0}]//Expand;
		Print["2---------> ",(tmp+(tmp/.{\[Rho]\[Rule]\[Eta],\[Eta]\[Rule]\[Rho]}))//Normal//Simplify];
		 ---------------------------- *)
		
	
(* some times there's warning "Unable to decide whether numeric quantity ... is equal to zero. Assuming it is. " expand tmp can prevent it but cause time consuming  *)
		If[OptionValue[OnebyOne]===True,
			tmp=Expand[Series[#,{Epsilon,0,ord}]&/@Expand[tmp]]
		,
			tmp=Expand[Series[tmp,{Epsilon,0,ord}]]
		];
		
		tmp=tmp/.null2->0;

(*--------------------------------------------------------------*)
		If[tmp===0,
			0
		,
		
		
		
			If[Length[tmp[[3]]]==1,
				list=tmp[[3]]tmp[[1]]^tmp[[4]]
			,
				list=Table[tmp[[3]][[i]] tmp[[1]]^(tmp[[4]]+i-1),{i,1,tmp[[5]]-tmp[[4]]}](* a list of result like { O(1/\[Epsilon]^2), O(1/\[Epsilon]), O(0), ... } *)
	
			];
					
							
									
													
			list=list/.{Log[Power[Pair[Momentum[p,di___],Momentum[p,di___]],po_]]:>-Log[Power[Pair[Momentum[p,D],Momentum[p,D]],-po]],
							Log[aa_ Power[Pair[Momentum[p,di___],Momentum[p,di___]],po_]]:>-Log[Power[Pair[Momentum[p,D],Momentum[p,D]],-po]/aa]};				
	(* -------------------------isolate Log[-p^2/4\[Pi]\[Mu]^2] for later Simplify ----------------------------*)
			If[ToLowerCase[ToString[subtract]]=="msbar",
				list=list/.{Log[k_ Pair[Momentum[p,di___],Momentum[p,di___]]]:>	
						log[-Pair[Momentum[p,D],Momentum[p,D]]/(ScaleMu^2)] +Log[-k]+2 Log[2]+ 2 Log[ScaleMu]+Log[Pi]-EulerGamma,		
					Log[Pair[Momentum[p,di___],Momentum[p,di___]]]:>
						log[-Pair[Momentum[p,D],Momentum[p,D]]/(ScaleMu^2)] - Pi I +2 Log[2]+ 2 Log[ScaleMu]+Log[Pi]-EulerGamma};
			,
				list=list/.{Log[k_ Pair[Momentum[p,di___],Momentum[p,di___]]]:>	
						log[-Pair[Momentum[p,D],Momentum[p,D]]/(4 Pi ScaleMu^2)]+Log[-k]+2 Log[2]+2 Log[ScaleMu]+Log[Pi],		
					Log[Pair[Momentum[p,di___],Momentum[p,di___]]]:>
						log[-Pair[Momentum[p,D],Momentum[p,D]]/(4 Pi ScaleMu^2)]- Pi I +2 Log[2]+2 Log[ScaleMu]+Log[Pi]};
			];(* sign of Pi I in later term is because mathematica take Log[-1]= Pi by default *)
	
			
			list=list/.{Log[xx_]:>PowerExpand[Log[xx]] ,  Power[Log[xx_],yy_]:>PowerExpand[Log[xx]]^yy};
	
	
	(* -------------------- MTD[a,b]\[Rule] MTD[a,b] + FVD[p,a]FVD[p,b]/SPD[p], then MTD[a,b]\[Rule] MTD[a,b]- FVD[p,a]FVD[p,b]/SPD[p] in the end------------------*)
			If[!FreeQ[list,Pair[LorentzIndex[__],LorentzIndex[__]]],

				list=list/.Pair[LorentzIndex[x_,dim___],LorentzIndex[y_,dim___]]:>
					null1[x,y]  Pair[LorentzIndex[x,dim],LorentzIndex[y,dim]]+Pair[Momentum[p,dim],LorentzIndex[x,dim]]Pair[Momentum[p,dim],LorentzIndex[y,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]]
				];
	
	
	(*-------------------------Simplify PolyGamma--------------------------------*)
			If[!FreeQ[list,PolyGamma],list=list//FullSimplify];
			(*If[!FreeQ[list,PolyGamma],

			list=list//Expand;
			list=(fact[Cases[#,aa_ PolyGamma[bb_,cc_]|aa_ Power[PolyGamma[bb_,cc_],power_]|PolyGamma[bb_,cc_]|Power[PolyGamma[bb_,cc_],power_]|
								aa_ Zeta[bb_]|aa_ Power[Zeta[bb_],power_]|Zeta[bb_]|Power[Zeta[bb_],power_]]]+(#/.{PolyGamma[___]->0,Zeta[___]->0}))&/@list;
			list=list/.fact[aa_]:>FullSimplify[Plus@@aa+null]/.null->0;
			];*)
	
	(* -----------------check non-local pole -----------------------*)
			tmplist=list/.{Power[Epsilon,_?Negative]->ieps,log[__]->ilog};				
			If[!FreeQ[ExpandAll[tmplist],ieps ilog], nlocal=False];	
			list=Collect[ExpandAll[list],Epsilon]/.log->Log;(* ExpandAll[] to cancel a bunch of terms *)
	
	
	(* ----------------------discard \[Epsilon] pole if non-local pole not involved ----------------------------*)
			If[(ToLowerCase[ToString[subtract]]=="ms")||(ToLowerCase[ToString[subtract]]=="msbar")&&nlocal,
				list=list/.Power[Epsilon,_?Negative]->0
			];
		
	(*------------gather by Lorentz structure-----------------*)
	(* make every term have (1/Epsilon)^_ , to make the Collect[] can collect terms by order; times null1[0,0] to make scalar results can also be collected *)		
			list=null1[0,0]list Epsilon^(-ord-1);
			list=Collect[#,null1[___]]&/@list;		
	(* simplify for each term with same lorentz structure, restore the correct order of Epsilon *)

			list=If[ToString[Head[#]]=="Plus",(Simplify[Epsilon^(ord+1)List@@#])//Total,Simplify[Epsilon^(ord+1)#]]&/@list;
			list=list//Total;
			

			tmp=list/.{Pair[LorentzIndex[x_,dim___],LorentzIndex[y_,dim___]]:>
					Pair[LorentzIndex[x,dim],LorentzIndex[y,dim]]-Pair[Momentum[p,dim],LorentzIndex[x,dim]]Pair[Momentum[p,dim],LorentzIndex[y,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]],null1[___]->1}
		]
	]
]

]






End[]
