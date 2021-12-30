(* ::Package:: *)

(* Wolfram Language package *)

QSimplify2::usage= "QSimplify2[expr_,ruless___] is a function to combine same Lorentz structure and simplify the accompany Gamma functions";


Begin["`Private`QSimplify2`"]

(*---------------------------------------------------------------*)

QSimplify2[expr_,ruless_List:{nullr}]:=Block[{tmp,fact,const1,const2,const3,identity,rules0,rules,null,nogamm,dot,qamm1,qamm2},

	tmp=expr//FCI//Expand;
	tmp=tmp/.Dot->dot;

	rules0=If[And@@(MatchQ[#,_Rule]&/@ruless),ruless, ToExpression[StringJoin[ToString[#],"[___]->1"]]&/@ruless];
	
	rules=Join[{Power[xx_,po_]/;!FreeQ[xx,Pair[___]|FeynAmpDenominator[___]]->1,Pair[___]->1,FeynAmpDenominator[___]->1,
					SUNT[___]->1,DiracGamma[___]->1,Eps[___]->1,DiracSigma[___]->1,dot[___]->1},rules0]//DeleteDuplicates;
	
	
	If[Head[tmp]===Plus,
		tmp=List@@tmp;
	
		tmp={Replace[#,rules,{1}],Replace[#,Except[Alternatives@@(#[[1]]&/@rules)]->1,{1}]}&/@tmp;
		tmp=Gather[tmp,Last[#1]==Last[#2]&];
	

		tmp=(Transpose[#]&/@tmp)/.{qfact1->Identity,dot->Dot};
		
	(*
		tmp=(Transpose[#]&/@tmp)/.{qfact1->Identity,I^(aa_EvenQ D+bb_):>(-1)^(aa/2 D)I^bb,I^(aa_OddQ D+bb_):>(-1)^((aa-1)/2 D)I^(D+bb),
								I^(aa_EvenQ D):>(-1)^(aa/2 D),I^(aa_OddQ D):>(-1)^((aa-1)/2 D)I^D};
		tmp=tmp/.{(-1)^(aa_Integer+bb_):>(-1)^aa identity[(-1)^bb]};
	*)
		tmp=qfact1[Plus@@#[[1]]//Expand] #[[2]][[1]]&/@tmp;
		
	
	];
	
	
	
		tmp=(tmp/.dot->Dot)/.qfact1[aa_]:>qfact1[aa/.qfact2[bb_]qfact2[cc_]:>qfact2[Simplify[bb cc/.qfact2->Identity]]];
		(*--------------------------------------------------- Simplify Gamma functions ------------------------------------------------*)
		
		tmp=tmp/.qfact1[aa_/;Head[aa]===Plus]:>(nogamm=(aa/.Power[qGamma[___],___]->0)/.qGamma[___]->0 ; qfact1[qfact2[nogamm] + aa - nogamm]);
		(*tmp=tmp/.qfact1[aa_]:>(nogamm=(aa/.Power[qGamma[___],___]->0)/.qGamma[___]->0;qfact1[qfact2[nogamm] + aa - nogamm]/.null->0);*)
		
		tmp=tmp/.qfact1[aa_/;Head[aa]===Plus]:>qfact1[List@@aa];
		
		tmp=tmp/.qGamma[aa_]:>qGamma[Expand[aa]];
		tmp=tmp/.qGamma[aa_Integer]/;Positive[aa]:>Gamma[aa];
		
		(* --------------------------------------  prepare for simplify ---------------------------------------------- *)
		(*  the struct of aa in qfact1 before simplify is
		             _          _                                                                                                                                                              _  _
		             |          | {{ qGamma[_*D]in numerator , qGamma[_*D]in denominator }   ,   {qGamma[_*D,n_] in numerator , qGamma[_*D,_] in denominator}  ,  single term/. qGamma->qamm1 or qamm2}|  |
		             | one type | {{ignore the addend n_, sort by _*D; the term with }   ,   {  ignore the power of qGamma;    [_*D+n_] -> [_*D,n_]   }  ,                   .                } |  |            
		             |          | {{same qGamma[_*D]^_.../qGamma[_*D]^_... is a type.   }   ,   {         prepare for find the max or min n_            }  ,                   .                } |  |             
		    qfact1[  |          | {                                                                           ...                                                                               |  |  ]
		             |           -                                                                                                                                                              -  |                            
		             |                                                      other types                                                                                                            |         
		             |                                                          ...                                                                                                                |
		             -                                                          ...                                                                                                               -
		  *)
		  
		
  (* --------  factors(qGamma[_*D+_]^p ...)/(qGamma[_*D+_]^n ...) 
           >>>>>> {(qGamma[_*D+_]^p...)/(qGamma[_*D+_]^n ...) , factors(qamm1[_*D,_]^p ...)/(qamm2[_*D,_]^n ...)}    ---------- *)
		tmp=tmp/.qfact1[aa_List]:>qfact1[{#/(#/.qGamma[___]->1),
						(#/.{Power[qGamma[cc_],dd_?Negative]/;Head[cc]===Plus:>qamm2[Replace[cc,{_Rational->0,_Integer->0},{1}],cc-Replace[cc,{_Rational->0,_Integer->0},{1}]]^dd,
										Power[qGamma[cc_],dd_?Negative]/;Head[cc]=!=Plus:>qamm2[cc,0]^dd})
						/. {qGamma[cc_]/;Head[cc]===Plus:>qamm1[Replace[cc,{_Rational->0,_Integer->0},{1}],cc-Replace[cc,{_Rational->0,_Integer->0},{1}]],
							qGamma[cc_]/;Head[cc]=!=Plus:>qamm1[cc,0]}}&/@(List@@aa)];
							
							
   (*      >>>>>>    { {(qGamma[_*D+_]^p ...) , (qGamma[_*D+_]^n ...)} , factors(qamm1[_*D,_]^p ...)/(qamm2[_*D,_]^n ...) }    ---------- *)
		tmp=tmp/.qfact1[aa_List]:>qfact1[{{#[[1]]/.Power[___,_?Negative]->1,(1/#[[1]])/.Power[___,_?Negative]->1},#[[2]]}&/@aa];
		
		
   (*     >>>>>> { {(qGamma[_*D]^p ...) , (qGamma[_*D]^n ...)} , {(qGamma[_*D,_] ...) , (qGamma[_*D,_] ...)} , factors(qamm1[_*D,_]^p ...)/(qamm2[_*D,_]^n ...)}  ------- *)
		tmp=tmp/.qfact1[aa_List]:>qfact1[{#[[1]]/.qGamma[bb_]/;Head[bb]===Plus:>qGamma[Replace[bb,{_Rational->0,_Integer->0},{1}]],
					(#[[1]]/.Power[bb_,cc_?Positive]:>bb)/.{qGamma[dd_]/;Head[dd]===Plus:>qGamma[Replace[dd,{_Rational->0,_Integer->0},{1}],dd-Replace[dd,{_Rational->0,_Integer->0},{1}]],qGamma[dd_]/;Head[dd]=!=Plus:>qGamma[dd,0]},
							#[[2]]}&/@aa];
								
(*----------------- soring by {(qGamma[_*D]^p ...) , (qGamma[_*D]^n ...)}  -------------------*)							
		tmp=tmp/.qfact1[aa_List]:>qfact1[Gather[aa,First[#1]==First[#2]&]];
		
	(*------------------------ Combine the Gamma functions ---------------------------*)	
		
	If[Head[tmp]===List,	
		tmp=Total[tmp/.qfact1[aa_List]:>qfact1[Map[qSimplify3,aa,{1}]//Total]]
	,	
		tmp=tmp/.qfact1[aa_List]:>qfact1[Map[qSimplify3,aa,{1}]//Total]
	]
]

(*
qamm1[];
qamm2[];
*)


(*---------------------------------------------------------------*)


qSimplify3[expr_List]:=Block[{tmp,list,nlist1,nlist2,dlist1,dlist2,result,rule1,rule2,qamm1,qamm2},

If[Length[expr]===1,
	
	tmp=Expand[expr[[1,3]]]/.qfact2[aa_]qfact2[bb_]:>qfact2[Simplify[aa bb/.qfact2->Identity]];
	tmp=tmp/.{qamm1[aa_,bb_]:>qGamma[aa+bb],qamm2[aa_,bb_]:>qGamma[aa+bb]}
(*	tmp=qfact2[Replace[tmp,qGamma[___]|Power[qGamma[___],___]->1,{1}]/.qfact2->Identity]Replace[tmp,Except[qGamma[___]|Power[qGamma[___],___]]->1,{1}]*)
,
(*------- get the _*D in qGamma[_*D]--------*)
	tmp=expr//Transpose;
	nlist1=tmp[[1,1,1]]/.Power[aa_,bb_]:>aa;
	nlist1=If[Head[nlist1]===Times,(List@@nlist1)/.qGamma[aa_]:>aa,{nlist1/.qGamma[bb_]:>bb}];
	dlist1=tmp[[1,1,2]]/.Power[aa_,bb_]:>aa;
	dlist1=If[Head[dlist1]===Times,(List@@dlist1)/.qGamma[aa_]:>aa,{dlist1/.qGamma[bb_]:>bb}];

(*----------- find the max or min of n_ in qGamma[_*D,n_] for this type ------------*)
	result=tmp[[3]];
	list=tmp[[2]]//Transpose;

	nlist2=(Cases[list[[1]],qGamma[#,aa_]:>aa,Infinity]//Min)&/@nlist1;
	dlist2=(Cases[list[[2]],qGamma[#,aa_]:>aa,Infinity]//Max)&/@dlist1;

(*  -------------replace qGamma[_*D+n_] that n_ is max or min -------------  *)
	rule1=Rule[qamm1[#[[1]],#[[2]]],qGamma[#[[1]]+#[[2]]]]&/@Transpose[{nlist1,nlist2}];
	rule2=Rule[qamm2[#[[1]],#[[2]]],qGamma[#[[1]]+#[[2]]]]&/@Transpose[{dlist1,dlist2}];

	result=(result/.rule1)/.rule2;
	
(*------------- replace qGamma[_*D+n_] -> (_*D+_)...qGamma[_*D + (max or min n_)] -------------*)
	rule1=(qamm1[#[[1]],bb_]:>Product[#[[1]]+i,{i,#[[2]],bb-1}]qGamma[#[[1]]+#[[2]]])&/@Transpose[{nlist1,nlist2}];
	rule2=(qamm2[#[[1]],bb_]:>qGamma[#[[1]]+#[[2]]]/Product[#[[1]]+i,{i,bb,#[[2]]-1}])&/@Transpose[{dlist1,dlist2}];

	result=(result/.rule1)/.rule2;
	result=Transpose[{Replace[#,qGamma[___]|Power[qGamma[___],___]->1,{1}]/.qfact2->Identity,Replace[#,Except[qGamma[___]|Power[qGamma[___],___]]->1,{1}]}&/@result];
	
	result=qfact2[Simplify[result[[1]]//Total]]result[[2,1]]/.{qamm1[aa_,bb_]:>qGamma[aa+bb],qamm2[aa_,bb_]:>qGamma[aa+bb]}

]
]




(*---------------------------------------------------------------*)




End[]
