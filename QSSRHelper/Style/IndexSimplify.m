(* ::Package:: *)

(* Wolfram Language package *)

(* Author: ShungHong Li *)





IndexSimplify::usage =
	"IndexSimplify[expr] simplify the dummy indices "	
	
	
Begin["`Private`IndexSimplify`"]



Options[IndexSimplify] = {
	Cyclic->False,
	NonCommutative->{},
	Contract->False,
	Lorentz->"Auto",
	Color->"Auto",
	Symmetry->"None"}






IndexSimplify[expr_,OptionsPattern[]]:=Block[{tmp,tmp2,tmp3,tmp4,power,warning,nonc,dot,times,null0,null1,
	lindex,dgamma,sigma,eps,pair,sindex,sunt,suntf,sunf,sund,sundelta,function,lor,tmpindx,indices,indxhead,rule1,rule2,rule3,symm={"null"}},

(* list of noncommutative objects *)
nonc=Join[OptionValue[NonCommutative],{DiracGamma,DiracSigma,SUNT}]//DeleteDuplicates;


tmp=expr//FCI//Expand;


If[ToLowerCase[ToString[OptionValue[Contract]]]=="true",tmp=Contract[tmp]//Expand];
(* Contract[] may hide the error in input, e.g. Contract[ FVD[q,u] FVD[l,u]^D ] -> SPD[l,q]^D, however, the FVD[l,u]^D is not acceptable. *)


(* extract commutative objects in noncommutative product *)

tmp=tmp/.Dot->dot;
tmp=tmp//.dot[aa___,bb0_ bb1_,cc___]/;FreeQ[nonc,Head[bb0]]:>bb0 dot[aa,bb1,cc];
tmp=tmp//.dot[aa___,bb_,cc___]/;FreeQ[nonc,Head[bb]]:>bb dot[aa,cc];
tmp=tmp//.{dot[aa___,bb_DiracGamma,cc_SUNT,dd___]:>dot[aa,cc,bb,dd],dot[aa___,bb_DiracSigma,cc_SUNT,dd___]:>dot[aa,cc,bb,dd]};
(* separate color and lorentz space *)
tmp=tmp/.dot[aa___,bb__SUNT,cc__DiracGamma,dd___]:>dot[bb]dot[aa,cc,dd];
tmp=tmp/.dot[aa___,bb__SUNT,cc__DiracSigma,dd___]:>dot[bb]dot[aa,cc,dd];


(*---  ---------main part---------  ---*)


(**---  simplify lorentz indices  ---**)
(* ignore whether the input is Lorentz covariant, merely collect terms differ by dummy indices. this procedure will not change the Lorentz covariance *)

tmp=tmp null1 tmp3[null1]//Expand;


(* e.g. c f[y^u] q^v +... -> c f[y^u] tmp3[q^v]+... *)
tmp=(tmp//.Pair[aa__]tmp3[cc__]/;!FreeQ[List[aa],LorentzIndex]:>tmp3[cc,Pair[aa]])//.Eps[aa__]tmp3[cc__]/;!FreeQ[List[aa],LorentzIndex]:>tmp3[cc,Eps[aa]];



(* e.g. {c f[y^u] tmp3[q^v], ...} -> {{times[c, f[y^u], tmp3[q^v]], times[c, f[y^u]], tmp3[q^v]}, ...} *)
tmp=If[Head[tmp]===Plus,List@@tmp,List[tmp]];
tmp=Replace[tmp,Times->times,{2},Heads->True]/.null1->1;
tmp=(Sort[#]&/@tmp)/.aa_tmp3:>Sort[aa];

(* replace the Heads to avoid potential problem *)
tmp=tmp/.{Eps->eps,DiracGamma->dgamma,DiracSigma->sigma,Pair->pair,SUNT->sunt,SUNTF->suntf,SUNF->sunf,SUND->sund,SUNDelta->sundelta}/.
		{LorentzIndex->lindex,SUNIndex->sindex};




(* options about symmetry *)
If[!FreeQ[ToLowerCase[ToString[#]]&/@OptionValue[Symmetry],"cyclic"],symm=Append[symm,"cyclic"]];
If[!FreeQ[ToLowerCase[ToString[#]]&/@OptionValue[Symmetry],"reverse"],symm=Append[symm,"reverse"]];


tmp=gatherdummy[tmp,{sigma,eps,lindex,sindex,$AL},If[MatchQ[OptionValue[Lorentz],_List],OptionValue[Lorentz],"Auto"],symm]/.{times->Times,tmp3->Times};



(**---  simplify color indices  ---**)

tmp=tmp tmp3[null1]null1;
tmp=tmp//.{tmp3[aa__]bb_sund:>tmp3[aa,bb],tmp3[aa__]bb_sunf:>tmp3[aa,bb]};
tmp=Replace[tmp,Times->times,{3},Heads->True]/.null1->1;
tmp=If[Length[#]>1,gatherdummy[#,{sunf,sund,sindex,lindex,$AC},If[MatchQ[OptionValue[Color],_List],OptionValue[Color],"Auto"],symm],{#}]&/@tmp;



(**---  refine  ---**)


tmp=(tmp/.{lindex->LorentzIndex,sindex->SUNIndex}/.
	{pair->Pair,eps->Eps,dgamma->DiracGamma,sigma->DiracSigma ,sunt->SUNT,suntf->SUNTF,sunf->SUNF,sund->SUND,sundelta->SUNDelta}/.
		{tmp3->Times,times->Times});
		

tmp=tmp//.dot[aa___,bb0_ bb1_,cc___]/;FreeQ[nonc,Head[bb0]]:>bb0 dot[aa,bb1,cc];
tmp=tmp//.dot[aa___,bb_,cc___]/;FreeQ[nonc,Head[bb]]:>bb dot[aa,cc];
tmp=tmp/.dot->Dot;



tmp=(Plus@@(Simplify[Plus@@#]&/@#))&/@tmp;


Plus@@(Simplify[#]&/@tmp)


]







(* gather the equivalent terms *)
gatherdummy[expr_,{symm1_,symm2_,index_,index2_,aindex_},dummy_,symmetry_]:=Block[{tmp,tmp2,position,indices,times,dot,dot2,dot3,n},



tmp=expr;



(* brutely enumerate all possible situation *)
	(* if treat terms in dot[] differ by cyclic are equivalent *)
If[!FreeQ[ToLowerCase[ToString[#]]&/@symmetry,"cyclic"],
	tmp=(#/.bb_dot:>(n=Length[bb];dot2@@Join[n,Table[dot@@Join[List@@bb[[j+1;;]],List@@bb[[1;;j]]],{j,0,n-1}]]))&/@tmp;
		
	tmp=(tmp2={#};
		While[!FreeQ[tmp2,dot2],

			tmp2=Flatten[
				(position=FirstPosition[#,dot2];
				Table[ReplacePart[#,position[[;;-2]]->Extract[#,Join[position[[;;-2]],{2,i}]]],{i,1,Extract[#,Join[position[[;;-2]],{1}]]}]
				)&/@tmp2]
		
		];tmp2)&/@tmp;
		

];




	(* if treat terms in dot[] differ by reverse are equivalent *)
If[!FreeQ[ToLowerCase[ToString[#]]&/@symmetry,"reverse"],
	tmp=(#/.bb_dot:>(n=Length[bb];dot2@@Join[n,Table[dot@@Join[List@@bb[[j+1;;]],List@@bb[[1;;j]]],{j,0,n-1}]]))&/@tmp;
		
	tmp=(tmp2=If[Head[#]===List,#,{#}];
		While[!FreeQ[tmp2,dot2],

			tmp2=Flatten[
				(position=FirstPosition[#,dot2];
				Table[ReplacePart[#,position[[;;-2]]->Extract[#,Join[position[[;;-2]],{2,i}]]],{i,1,Extract[#,Join[position[[;;-2]],{1}]]}]
				)&/@tmp2]
		
		];tmp2)&/@tmp;
];





(* superficially gather the terms merely differ by dummy indices (with the free indices omitted) *)
(* by #[[2]] and #[[3]] in {_,_,_,_} in the output of gatherdummy2 *)
If[!FreeQ[ToLowerCase[ToString[#]]&/@symmetry,"reverse"|"cyclic"],
	(* brutely enumerate all possible situation to see whether exist terms differ by cyclic or reverse *)
	tmp=((gatherdummy2[#,{symm1,symm2,index,index2,aindex},dummy]/.{aa_,bb_,cc_,dd_}:>{aa,{bb,cc},dd})&/@#)&/@tmp;

	tmp2={};
	While[Length[tmp]>0,
		position=Position[tmp,tmp[[1,1,2]]];
		position=#[[;;2]]&/@position;
		position=position//.{aa___,{b1_,b2_},{b1_,b3_},cc___}:>{aa,{b1,b2},cc};
		(* e.g. for dot[y^u,y^v,y^v,y^u] and dot[y^v,y^v,y^u,y^u] with cyclic symmetry, each generate 4 terms:
		   {{u,v,v,u}             {{v,v,u,u}
		~   {v,v,u,u}    and   ~   {v,u,u,v}    respcetively,  but there are only 2 dummy structures (with out cyclic symmetry) 
		    {v,u,u,v}              {u,u,v,v}    choose the first matched case for each term
		    {u,u,v,v}}             {u,v,v,u}} *)

		(* extract the terms differ by cyclic or reverse of dot[...]; restore to the form of the output of gatherdummy2 *)
		tmp2=Join[tmp2,{Replace[Extract[tmp,position],{aa_,bb_,cc_}:>{aa,bb[[1]],bb[[2]],cc},{1}]}];

		(* remove equivalent terms *)
		position={#[[1]]}&/@position;
		tmp=Delete[tmp,position];

	];
	
	tmp=tmp2;
	
,	
	(* if the order of terms in dot is relevant *)
	tmp=gatherdummy2[#,{symm1,symm2,index,index2,aindex},dummy]&/@tmp;
	
	tmp=Gather[tmp,((#1[[2]]===#2[[2]])&&(#1[[3]]===#2[[3]]))&];
];





(* rename the dummy indices *)
tmp=If[Length[#]>1,
		If[MatchQ[dummy,_List],
			(* use specified dummy indices *)
			indices=If[Length[dummy]<Length[#[[1,4]]],
						Join[dummy,Table[aindex[Unique[]],Length[#[[1,4]]]-Length[dummy]]]
					,
						dummy[[;;Length[#[[1,4]]] ]]	
					]
		,
			indices=Table[aindex[Unique[]],Length[#[[1,4]]]]
		];
		
		(#[[1]]/.Thread[Rule[#[[4]],indices]])&/@#
	,
		{#[[1,1]]}
	]&/@tmp

]





(* extract the sturcture of dummy indices *)
(* the output has the form: {term, term that depress the indices and remove the commutative part, the position of dummy indices, dummy indices } *)

gatherdummy2[expr_,{symm1_,symm2_,index_,index2_,aindex_},dummy_]:=Block[{tmp,tmp3,tmp4,times,sym1=symm1,sym2=symm2,
	indxx=index,indxx2=index2,function,lor,col,tmpindx,indxhead,indices,warning},



tmp={expr,expr/.bb_tmp3:>1,expr/.times[aa___,bb_tmp3,cc___]:>bb};


(* e.g. 
{{times[c, f[y^u], g[sigma^uv], tmp3[q^v]], times[c, f[y^u], g[sigma^uv]], tmp3[q^v]},
 ...} 
-> 
{{times[c, f[y^u], g[sigma^uv]], tmp3[q^a]], times[c, f[y^u], g[sigma[{sigma,{u,v}}]]], tmp3[q^a], {u, {sigma,u}, {sigma,v}, a} },
 ...} *)
(* for DiracGamma[., .], eps[., ., ., .], the position of lorentz index is irrelevant; label the index in a different way *)
tmp={#[[1]],#[[2]],#[[3]],({#[[2]],#[[3]]}/.{aa_sym2:>(aa/.indxx[bb_,___]:>indxx[{sym2,bb}]),aa_sym1:>(aa/.indxx[bb_,___]:>indxx[{sym1,bb}])})}&@tmp;
tmp={#[[1]],#[[2]],#[[3]],Join[Cases[#[[4,1]],aa_indxx:>aa[[1]],Infinity],Cases[#[[4,2]],aa_indxx:>aa[[1]],Infinity]]}&@tmp;


(* if involve dummy index that appear in more than two place *)
warning=(Times@@Replace[#[[4]], {_,aa_}:>aa,{1}])&@tmp;
If[!FreeQ[warning,Power[aa_,bb_]/;bb>2],Print["QSSRHelper don't know how to interpret the Lorentz structure. "]];



(* e.g. 
{{times[c, f[y^u], g[y^u]], tmp3[q^v]], times[c, f[y^u], g[y^u]], tmp3[q^v], {u,u,v} },
 ...} 
-> 
{{times[c, f[y^u], g[y^u]], tmp3[q^v]], f[y^lor]g[y^lor]q^lor, times[function[f,u], function[g,u], function[pair,v]], {u,u,v} },
 ...} *)
tmp={#[[1]],Replace[#[[2]],aa_/;FreeQ[aa,indxx]->1,{1}],
	(* remove terms not involve LorentzIndex *)
	Replace[#[[3]],aa_/;FreeQ[aa,indxx]->1,{1}],#[[4]]}&@tmp;

tmp={#[[1]],
	#[[2]]#[[3]]/.{indxx[aa_,bb___]:>indxx[lor,bb],indxx2[aa_,bb___]:>indxx2[col]}
	(* depress the LorentzIndex and SUNTIndex*),

	((times@@Join[List@@#[[2]],List@@#[[3]]])/.
		{aa_sym2:>sym2[indxx[{sym2,Cases[aa,bb_indxx:>bb[[1]],Infinity]} ]],aa_sym1:>sym1[indxx[{sym1,Cases[aa,bb_indxx:>bb[[1]],Infinity]}]]})
	(* label the LorentzIndex in sym2 and sym1 in a different way *)

	,#[[4]]}&@tmp;


tmp={#[[1]],#[[2]],
	Replace[#[[3]],aa_:>(function[Head[aa],Cases[aa,bb_indxx:>bb[[1]],Infinity]]),{1}]
	(* collect functions' Head and the involved LorentzIndex *)

	,#[[4]]}&@tmp;



(* remove junk *)
tmp=(tmp/.function[_,{}]:>1)/.{aa_tmp3:>DeleteCases[aa,1,{1}],aa_times:>DeleteCases[aa,1,{1}]};


(* #[[4]] -> the dummy indices in #[[4]] *)
tmp={#[[1]],#[[2]]/.{times->Times,tmp3->Times},#[[3]],

	(* label the dummy indices, e.g. {u, a, {eps,a}, {eps,b}, {eps,c}, {eps,d}, e, c, b, f} -> {u, a^2, d, e, c^2, b^2, f};
	label in this way to avoid to dicsuss the positon of dummy index in eps or DiracSigma *)
	#[[4]]//.{{aa___,{hh_,b_},cc___,b_,dd___}:>{aa,cc,b^2,dd},{aa___,b_,cc___,{hh_,b_},dd___}:>{aa,b^2,cc,dd},{aa___,{hh1_,b_},cc___,{hh2_,b_},dd___}:>{aa,b^2,cc,dd}}//.
		{aa___,b_,cc___,b_,dd___}:>{aa,b^2,cc,dd}
	}&@tmp;
		
		
tmp={#[[1]],#[[2]]/.{times->Times,tmp3->Times},#[[3]],(Cases[#[[4]],Power[aa_,2]:>aa,{1}])}&@tmp;




(* {function[head1, {c,u,v,a,u,b}], function[head2, {a,f,e,c,f,g}], ...} -> 
	{function[head1, {{head2,2}, 3, 1, {head2,7}, 3, 2}], function[head2, {{head1,2}, 3, 1, {head1,7}, 3, 1}], ...} *)
(* label the nth dummy index by nth prime number *)
tmp={#[[1]],#[[2]],(tmp4=#[[3]];
	For[i=1,i<Length[ #[[4]] ]+1,i++,
		tmpindx=Position[tmp4,#[[4]][[i]] ];

		If[Dimensions[tmpindx]=={2,3},(* if not involved in eps, or DiracSigma *)
			If[tmpindx[[1,1]]==tmpindx[[2,1]],
				tmp4=tmp4/.#[[4]][[i]]->Prime[tmpindx[[1,3]] ](* if in the same funciton *)
			,
				tmp4[[tmpindx[[1,1]],2,tmpindx[[1,3]] ]]=indxhead[tmp4[[tmpindx[[2,1]],1 ]], Prime[tmpindx[[1,3]] ]];
				tmp4[[tmpindx[[2,1]],2,tmpindx[[2,3]] ]]=indxhead[tmp4[[tmpindx[[1,1]],1 ]], Prime[tmpindx[[2,3]] ]]  
			]
		,

			tmpindx=tmpindx/.{aa_,bb_}/;Length[bb]<Length[aa]:>{bb,aa};

			(* if dummy index appear in one of eps of DiracGamma; label the dummy index by the position of the index that not in eps and DiracGamma *)
			(* thus, e.g. f1[y^u,y^a] eps[u,v,a,b] -> function[f1,{indxhead[eps,2], indxhead[eps,3] }] function[eps,{indxhead[f1,2],1,indxhead[f1,3],1}] 
												   -> function[f1,{indxhead[eps,2], indxhead[eps,3] }] function[eps,indxhead[f1,2]indxhead[f1,3]].
				which avoid the discussion of the order of u,a in eps[u,v,a,b]] 
			 *)
			If[Length[tmpindx[[1]] ]==3,
				If[tmpindx[[1,1]]==tmpindx[[2,1]],
					tmp4=tmp4/.#[[4]][[i]]->Prime[tmpindx[[1,3]] ](* if in the same funciton *)
				,
					tmp4[[tmpindx[[1,1]],2,tmpindx[[1,3]] ]]=indxhead[tmp4[[tmpindx[[2,1]],1 ]], Prime[tmpindx[[1,3]] ]];
					tmp4[[tmpindx[[2,1]],2,tmpindx[[2,3]],2,tmpindx[[2,5]] ]]=indxhead[tmp4[[tmpindx[[1,1]],1 ]], Prime[tmpindx[[1,3]] ]]  
				]				

			,

				If[tmpindx[[1,1]]==tmpindx[[2,1]],
					tmp4=tmp4/.#[[4]][[i]]->Prime[tmpindx[[1,3]] ](* if in the same funciton *)
				,
					tmp4[[tmpindx[[1,1]],2,tmpindx[[1,3]],2,tmpindx[[1,5]] ]]=indxhead[tmp4[[tmpindx[[2,1]],1 ]], Prime[tmpindx[[1,3]] ]];
					tmp4[[tmpindx[[2,1]],2,tmpindx[[2,3]],2,tmpindx[[2,5]] ]]=indxhead[tmp4[[tmpindx[[1,1]],1 ]], Prime[tmpindx[[1,3]] ]]  
				]
			]
		] 
	];
	
	tmp4/.function[head_,indx_]:>function[head,Replace[indx,Except[_Integer|_List|_indxhead]->1,{1}]]),
	
	#[[4]]}&@tmp;


tmp=tmp/.function[head_,indx_]:>function[head,indx/.{{sym1,aa_}:>{sym1,Times@@aa},{sym2,aa_}:>{sym2,Times@@aa}}];




(* times -> Times to avoid discuss the order of functions *)
tmp={#[[1]],#[[2]]/.times->Times,#[[3]]/.times->Times,#[[4]]}&@tmp



]






End[]	
