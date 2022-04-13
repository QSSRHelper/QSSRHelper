(* ::Package:: *)

(* Wolfram Language package *)

(* Author: ShungHong Li *)




TryReduce::usage =
	"TryReduce[expr_,momentums_List] is a function to check whether a feynman integral is reducible;
        for integrate involve 2-loop propagator type diagram, the 2-loop structure will be detect can convert to TARCER notation;
		for reducible feynman integral, it returns: {1, momentum_list,expr};
		for integral involve tadpole, e.g. Integrate over k1, it returns: {1,{___,k1,0},expr}};
		the momentum_list give a list of momentums, along which can recursively integrate the integral.
		if 2-loop propagator type integral involved, the 2-loop momentum will not shown in the momentum_list.
		for non-reducible feynman integral, it returns: {0, part of momentums which can recursively integrate,expr};
		"
		
		
		

Begin["`Private`TryReduce`"]


	
	
		
Options[TryReduce] = {
	toTFI->True,
	EvaluateTwoLoop->False,
	ShowSteps->False,
	Contract->True}




TryReduce[expr_,p_Symbol,rules___Rule]:=TryReduce[expr,{p},rules]




TryReduce[expr_,mom_List,OptionsPattern[]]:=Block[{numerator,numerator2,tmp,pair2,head,null,count,list,mom1=mom,mom0,tmp2loop,tmp2=1,tmp22,tmp3,tmp4,i,tmprule,mom00,tarcer,
tnumerator,twoloopm,twoloopm2,tarcer2,null0,pp,$AM,tmp5,mom05,m,list1={},reducible=1,tadpole=False,mom2,mom3,jacobi,
totfi=ToLowerCase[ToString[OptionValue[toTFI]]],e2loop=ToLowerCase[ToString[OptionValue[EvaluateTwoLoop]]],steps=ToLowerCase[ToString[OptionValue[ShowSteps]]]},

tmp=expr//FCI;

If[!FreeQ[tmp,PropagatorDenominator[bb_/;!And@@(FreeQ[bb,#]&/@mom1),aa_/;aa=!=0]],
	Print["Massive propagator involved! Stop the recursive integral."];Abort[]
];



(*--- if invole noncommutative product ---*)
If[!FreeQ[tmp,DiracTrace[a_]/;!FreeQ[a,DiracGamma[Momentum[aa_/;!And@@(FreeQ[aa,#]&/@mom1),dim___],dim___]]],
	If[steps=="true",Print["Evaluate the DiracTrace..."]];
	tmp=tmp/.DiracTrace[aa_]:>DiracTrace[aa,DiracTraceEvaluate->True]
];

(* if GammaScheme not specified, the DiracTrace may not evaluated *)
If[!FreeQ[tmp,aa_DiracTrace/;(Or@@(!FreeQ[aa,#]&/@pp))],
	Print["DiracTrace involved but haven't been evaluated!"];Abort[]
];


If[!FreeQ[tmp,DiracGamma[Momentum[aa_/;!And@@(FreeQ[aa,#]&/@mom1),dim___],dim___]],
	If[steps=="true",Print["Uncontract GSD..."]];
	tmp=QExpand[tmp,mom1]
];



tmp=tmp//Expand;



(*-------- Collect, e.g. (x^2+2xy+y^2)->(x+y)^2 ----------*)

If[!FreeQ[tmp,Power[aa_Plus,nn_Negative]/;!FreeQ[aa,Pair]],
	tmp=tmp/.Power[aa_Plus,nn_Negative]:>Power[Factor[aa],nn]
];(*  1/(a x^2 + 2a xy +a y^2) -> 1/(a(x+y)^2) *)


(**--- further try to collect momentums ---**)
tmp=tmp/.Power[aa_Plus,nn_]/;!FreeQ[aa,Momentum[___]]:>Power[aa/.Pair[Momentum[a_,dim___],Momentum[b_,dim___]]:>pair2[a,dim]pair2[b,dim],nn];
tmp=tmp/.Power[aa_,nn_]/;!FreeQ[aa,pair2[___]]:>Power[Factor[aa]/.bb1_ pair2[bb_,dim___]:>pair2[bb1 bb,dim],nn];
tmp=(tmp//.pair2[aa_,dim___]+pair2[bb_,dim___]:>pair2[aa+bb,dim])/.pair2[aa_,dim___]:>Pair[Momentum[aa,dim],Momentum[aa,dim]]^(1/2);




(* if involve more than one term *)
If[ToString[Head[tmp]]=="Plus",
	tmp=TryReduce[#,mom1,toTFI->totfi,EvaluateTwoLoop->e2loop,ShowSteps->False]&/@(List@@tmp);
	tmp=Flatten[tmp/.{nn_Integer,listt_List,aa_}:>head[nn,listt,aa]]/.head->List

,

(*---------- get the momentum of propagators ----------*)
	tmp=tmp/.Power[aa_FeynAmpDenominator,bb_Integer]/;Positive[bb]:>(aa/.FeynAmpDenominator[cc___]:>FeynAmpDenominator@@Flatten[Table[{cc},bb]]);
	tmp=(tmp/.PropagatorDenominator[aa_,0]:>mom0[aa/.Momentum[bb_,___]:>bb,1,1])/.FeynAmpDenominator->Times;

	tmp=tmp/.Power[Pair[Momentum[aa_,dim___],Momentum[aa_,dim___]],power_]/;!(IntegerQ[power]&&Positive[power]):>mom0[aa,1,-power];
	tmp=tmp/.Power[mom0[aa1_,aa2_,aa3_],power_]:>mom0[aa1,aa2^(2power),aa3 power];

	numerator=tmp/.{mom0[___]->1};
	
	
	(* Expand D-4 or 4 dimensional momenrum to D dimensional momentum with D-4 or 4 dimensional metirc *)
	numerator=numerator/.{Power[bb_Pair,po_]/;Or@@(!FreeQ[bb,Momentum[#,D-4]|Momentum[#,4]]&/@mom):>QExpand[bb^po,mom],bb_Pair/;Or@@(!FreeQ[bb,Momentum[#,D-4]|Momentum[#,4]]&/@mom):>QExpand[bb,mom]};
	
	numerator=numerator/.aa_Eps/;Or@@(!FreeQ[aa,Momentum[#,___]]&/@mom):>QExpand[aa,mom];
	
	
	
	(* isloate the terms inolve loop momentums *)
	numerator2=Replace[null null0 numerator,aa_/;Or@@(!FreeQ[aa,Momentum[#,___]]&/@mom)->1,{1}]/.{null->1,null0->1};(* terms without loop momentums *)
	numerator=Replace[null null0 numerator,aa_/;And@@(FreeQ[aa,Momentum[#,___]]&/@mom)->1,{1}]/.{null->1,null0->1};(* terms involve loop momentums *)
	
	
	
	tmp=List@@Replace[null tmp,Except[mom0[___]]->1,{1}];


(**--- gather the equivalent momentum, e.g. 2k-q ~ k-q/2; counter the factor and exponent, e.g. (5k+5p)^3 => mom0[5k+5p,1,3]=> mom0[k+p,5^(2*3),3] ---**)
	tmp=tmp//.{ll0___,mom0[aa1_,aa2_,aa3_],ll1___,mom0[ bb1_,bb2_,bb3_],ll2___}/;NumberQ[Simplify[aa1/bb1] ]:>{ll0,mom0[aa1,aa2 bb2 Simplify[bb1/aa1]^(2bb3),aa3+bb3],ll1,ll2};
	tmp=tmp/.{mom0[aa_ bb_,cc_,dd_]/;NumericQ[aa]:>mom0[bb,cc aa^(2dd),dd],mom0[aa_ b1_+ aa_ b2_,cc_,dd_]:>mom0[b1+b2,cc aa^(2dd),dd],
						mom0[aa_ b1_+ aaa_ b2_,cc_,dd_]/;(aaa/aa==-1):>mom0[b1-b2,cc aa^(2dd),dd]};


	
(*--- count the involved propagators for each loop momentum ---*)

	count=Outer[!FreeQ[#1,#2|-#2]&,tmp,mom1]//Boole//Transpose;
	list=(Plus@@#)&/@count;




(*-------------------------------------------------------------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------------------------------------------------------------*)
(*----------------------------- gather nonreducible 2-loop momentum ----------------------------------*)

(* understand the structure of tmp3, e.g. {{{k1,3},{1,0,1,0,0,1,...}},...}

	tmp:              k1-p, k2-p,  k1,  k2, p-q, k1-k2

	k1 :   {{{k1,3}, { 1   ,  0  , 1 ,  0,   0,   1  }},
	k2 :    {{k1,3}, { 0   ,  1  , 0 ,  1,   0,   1  }},
	p  :    {{p,3} , { 1   ,  1  , 0 ,  0,   0,   1  }}}
*)


	tmp3= DeleteCases[Transpose[{Transpose[{mom1,list}],count}],aa_/;aa[[1,2]]=!=3];

(* one can directely write a sort of rules to find the 2-loop structure, but it will be very long without some refinement about the momentum *)
(* the tarcer[...] have form: tarcer[{v1,v2,v3,v4,v5},{k1,k2,p,{rule1,rule2}}] now; the k1, k2 and p indicate k1, k2 and external momentum;
 the rule1, rule2 will used to shift or rescale the momoentum later. *)



	While[Length[tmp3]>1,

		For[i=1,i<Length[tmp3],


			If[Plus@@(tmp3[[1,2]]tmp3[[1+i,2]])==1,
				tmprule=(Plus@@(tmp tmp3[[1,2]]tmp3[[1+i,2]]))[[1]];(* (a k1 + b k2) -> (k1 -k2) or (a k1 + b k2 + c p)-> (k2 -> k2/b - c/b) -> (k1 - k2), 
				treat one of tmp3[[1,1,1]] and tmp3[[1+i,1,1]] as k2; generate rules to unify the momentum *)

				tmprule=tmprule/.{tmp3[[1,1,1]]+ tmp3[[1+i,1,1]]+cc_:>{tmp3[[1,1,1]]->- tmp3[[1,1,1]],tmp3[[1+i,1,1]]->tmp3[[1+i,1,1]]-cc},
								aa_ tmp3[[1,1,1]]+ tmp3[[1+i,1,1]]+cc_:>{tmp3[[1,1,1]]->-1/aa tmp3[[1,1,1]],tmp3[[1+i,1,1]]->tmp3[[1+i,1,1]]-cc},
								tmp3[[1,1,1]]+bb_ tmp3[[1+i,1,1]]+cc_:>{tmp3[[1+i,1,1]]->-tmp3[[1+i,1,1]]/bb-cc/bb},
								aa_ tmp3[[1,1,1]]+bb_ tmp3[[1+i,1,1]]+cc_:>{tmp3[[1,1,1]]->-1/aa tmp3[[1,1,1]],tmp3[[1+i,1,1]]->tmp3[[1+i,1,1]]/bb-cc/bb}}/.{
													tmp3[[1,1,1]]+ tmp3[[1+i,1,1]]:>{tmp3[[1,1,1]]->- tmp3[[1,1,1]]},
													aa_ tmp3[[1,1,1]]+ tmp3[[1+i,1,1]]:>{tmp3[[1,1,1]]->-1/aa tmp3[[1,1,1]]},
													tmp3[[1,1,1]]+bb_ tmp3[[1+i,1,1]]:>{tmp3[[1+i,1,1]]->-tmp3[[1+i,1,1]]/bb},
													aa_ tmp3[[1,1,1]]+bb_ tmp3[[1+i,1,1]]:>{tmp3[[1,1,1]]->-1/aa tmp3[[1,1,1]],tmp3[[1+i,1,1]]->tmp3[[1+i,1,1]]/bb}};
 

(**--- unify the momentum and find 2-loop structure, e.g. k1+q,2k2-q,p-k1,2k2+p,k1+2k2 ->(k1->k1-q,k2->(-k2+q)/2)) -> k1,k2,k1-(p+q),k2-(p+q),k1-k2 ---**)
				tmp2loop=Plus@@(tmp (tmp3[[1,2]]tmp3[[1+i,2]])/.tmprule);
				tmp2loop=tmp2loop(Times@@DeleteCases[tmp (tmp3[[1,2]]+tmp3[[1+i,2]]-2tmp3[[1,2]]tmp3[[1+i,2]]),0]/.tmprule/.{mom0[aa_ tmp3[[1,1,1]],cc_,dd_]:>mom0[tmp3[[1,1,1]],cc aa^(2dd),dd],
																													mom0[aa_ tmp3[[1+i,1,1]],cc_,dd_]:>mom0[tmp3[[1+i,1,1]],cc aa^(2dd),dd],
																													mom0[aa_ tmp3[[1,1,1]]+bb_,cc_,dd_]:>mom0[tmp3[[1,1,1]]+bb/aa,cc aa^(2dd),dd],
																													mom0[aa_ tmp3[[1+i,1,1]]+bb_,cc_,dd_]:>mom0[tmp3[[1+i,1,1]]+bb/aa,cc aa^(2dd),dd]});

(* find 2-loop structure *)
				tmp2loop=tmp2loop//.{mom0[aa1_,aa2_,aa3_]mom0[bb1_,bb2_,bb3_]mom0[aa1_+cc_,ac2_,ac3_]mom0[bb1_+cc_,bc2_,bc3_]mom0[aa1_-bb1_,ab2_,ab3_]
									:>mom00[-cc,1,1]1/(aa2 bb2 ab2 ac2 bc2)tarcer[{aa3,bb3,ac3,bc3,ab3},{aa1,bb1,-cc,{tmprule,1->1}}],
								mom0[aa1_+bb_,aa2_,aa3_]mom0[bb1_+bb_,bb2_,bb3_]mom0[aa1_+cc_,ac2_,ac3_]mom0[bb1_+cc_,bc2_,bc3_]mom0[aa1_-bb1_,ab2_,ab3_]
									:>mom00[bb-cc,1,1]1/(aa2 bb2 ab2 ac2 bc2) tarcer[{aa3,bb3,ac3,bc3,ab3},{aa1,bb1,bb-cc,{tmprule,{aa1->aa1-bb,bb1->bb1-bb}}}]};
								(* the mom00[aa_,1,1] is added to indicate the 2-loop can reduce to a propagator with momentum aa, the  1,1] is not important *)



				If[!FreeQ[tmp2loop,tarcer],

					tmp=tmp(1+tmp3[[1,2]]tmp3[[1+i,2]]-(tmp3[[1,2]]+tmp3[[1+i,2]]));
					tmp2=tmp2 tmp2loop;
					tmp3=Delete[tmp3,1+i];
					Break[]

				,
					i=i+1
				];

			,
				i=i+1
			];
		];

		i=1;
		tmp3=Delete[tmp3,1];
	];


(* remove the momentum already integrated *)
	mom1=If[FreeQ[tmp2,tarcer[ll0_,ll1_,ll2_]/;!FreeQ[ll2[[;;2]],#|-#]], #, 0]&/@mom1;
	mom1=DeleteCases[mom1,0];
(* update count & list *)
	count=Outer[!FreeQ[#1,#2|-#2]&,tmp,mom1]//Boole//Transpose;
	list=(Plus@@#)&/@count;



(**---------------------- further to try find 2-loop structure ---------------------------**)
(* e.g. k1+k2+p,k2+p,k1+k2+q,k2+q,k1 -> (k1->k1-k2 , k2->k2-p) -> k1,k2,k1-(p-q),k2-(p-q),k1-k2 *)

	tmp3=DeleteCases[DeleteCases[Transpose[{Transpose[{mom1,list}],count}],aa_/;aa[[1,2]]=!=3],aa_/;FreeQ[tmp,mom0[aa[[1,1]],___]] ];
	tmp4=DeleteCases[Transpose[{Transpose[{mom1,list}],count}],aa_/;aa[[1,2]]=!=4];


	While[Length[tmp3]>0,

		For[i=1,i<Length[tmp4]+1,

(*if need shift the momentum, e.g. k1+l+k2+p,k2+p,k1+l+k2+q,k2+q,k1+l -> (k1->k1-l) -> k1+k2+p,k2+p,k1+k2+q,k2+q,k1*)

			tmprule=(Plus@@(tmp(tmp3[[1,2]]-tmp3[[1,2]]tmp4[[i,2]])))[[1]];
			If[!FreeQ[tmprule,Plus],
				tmprule=tmprule/.{aa_ tmp3[[1,1,1]]+bb_:>(tmp3[[1,1,1]]->tmp3[[1,1,1]]/aa-bb/aa),tmp3[[1,1,1]]+bb_:>(tmp3[[1,1,1]]->tmp3[[1,1,1]]-bb)},
				tmprule=1->1;
			];


			tmp2loop=Times@@DeleteCases[tmp (tmp3[[1,2]]+tmp4[[i,2]]-tmp3[[1,2]]tmp4[[i,2]]),0]/.{mom0[aa_ tmp3[[1,1,1]]+bb_,cc_,dd_]:>mom0[tmp3[[1,1,1]]+bb/aa,cc aa^(2dd),dd],
																								mom0[aa_ tmp4[[i,1,1]]+bb_,cc_,dd_]/;FreeQ[bb,tmp3[[1,1,1]] ]:>mom0[tmp4[[i,1,1]]+bb/aa,cc aa^(2dd),dd]};


(*find 2-loop structure*)
			tmp2loop=tmp2loop//.{mom0[tmp3[[1,1,1]]+aa1_,aa2_,aa3_]mom0[tmp4[[i,1,1]],bb2_,bb3_]mom0[tmp3[[1,1,1]]+cc1_,cc2_,cc3_]mom0[tmp4[[i,1,1]]+dd1_,dd2_,dd3_]mom0[tmp3[[1,1,1]],ee2_,ee3_]
									/;(NumericQ[Simplify[aa1/tmp4[[i,1,1]] ]]&&(Simplify[aa1/tmp4[[i,1,1]]]==Simplify[cc1/(tmp4[[i,1,1]]+dd1)]))
										:>Simplify[aa1/tmp4[[i,1,1]]]^(2bb3+2dd3)/(aa2 bb2 cc2 dd2  ee2) mom00[-dd1 Simplify[aa1/tmp4[[i,1,1]]],1,1]*
											tarcer[{aa3,bb3,cc3,dd3,ee3},{tmp3[[1,1,1]],tmp4[[i,1,1]],-dd1 Simplify[aa1/tmp4[[i,1,1]]],{tmprule,tmp3[[1,1,1]]->tmp3[[1,1,1]]-aa1,tmp4[[i,1,1]]->tmp4[[i,1,1]]/Simplify[aa1/tmp4[[i,1,1]]]}}],
							mom0[tmp3[[1,1,1]]+aa1_,aa2_,aa3_]mom0[tmp4[[i,1,1]]+bb1_,bb2_,bb3_]mom0[tmp3[[1,1,1]]+cc1_,cc2_,cc3_]mom0[tmp4[[i,1,1]]+dd1_,dd2_,dd3_]mom0[tmp3[[1,1,1]],ee2_,ee3_]
								/;(NumericQ[Simplify[aa1/(tmp4[[i,1,1]]+bb1) ]]&&(Simplify[aa1/(tmp4[[i,1,1]]+bb1)]==Simplify[cc1/(tmp4[[i,1,1]]+dd1)]))
									:>Simplify[aa1/(tmp4[[i,1,1]]+bb1)]^(2bb3+2dd3)/(aa2 bb2 cc2 dd2  ee2)mom00[Simplify[(bb1-dd1)aa1/(tmp4[[i,1,1]]+bb1)],1,1]tarcer[{aa3,bb3,cc3,dd3,ee3},{tmp3[[1,1,1]],tmp4[[i,1,1]],Simplify[(bb1-dd1)aa1/(tmp4[[i,1,1]]+bb1)]
											,{tmprule,{tmp3[[1,1,1]]->tmp3[[1,1,1]]-tmp4[[i,1,1]]Simplify[aa1/(tmp4[[i,1,1]]+bb1)],tmp4[[i,1,1]]->tmp4[[i,1,1]]-bb1},tmp4[[i,1,1]]->tmp4[[i,1,1]]/Simplify[aa1/(tmp4[[i,1,1]]+bb1)]}}]};
							(* the mom00[aa_,1,1] is added to indicate the 2-loop can reduce to a propagator with momentum aa, the ',1,1]' is not important *)

			If[!FreeQ[tmp2loop,tarcer],

				tmp=tmp(1+tmp3[[1,2]]tmp4[[i,2]]-(tmp3[[1,2]]+tmp4[[i,2]]));
				tmp2=tmp2 tmp2loop;
				tmp4=Delete[tmp4,i];
				Break[]
			];

			i=i+1
		];

		i=1;
		tmp3=Delete[tmp3,1]
	];


(*--- times the jacobi if the momentum have been rescaled ---*)
	tmp2=tmp2/.tarcer[ll1_,ll2_]:>(jacobi=Flatten[ll2[[4]]]/.{(ll2[[1]]->aa_ ll2[[1]]):>Abs[aa]^D,(ll2[[2]]->aa_ ll2[[2]]):>Abs[aa]^D,(ll2[[1]]->aa_ ll2[[1]]+bb_):>Abs[aa]^D,(ll2[[2]]->aa_ ll2[[2]]+bb_):>Abs[aa]^D};
								jacobi=Times@@DeleteCases[jacobi,Rule[_,_]];
								jacobi tarcer[ll1,ll2]);



(*-------------------------------------------------------------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------------------------------------------------------------*)
(*----------- to gather the numerators belong to the 2-loop integral ------------*)
(*--- combine 'numerator' and 'tmp2' ; find the SPD[]&FVD[] which involve k1,k2 ---*)

(* Expand, e.g. SPD[k1,k3] -> FVD[k1,u]FVD[k3,u], FVD[k1-k3,mu]->FVD[k1,mu]-FVD[k3,mu] with k1, k3 is loop momentum in two diffenent 2-loop *)
	If[Exponent[tmp2/.tarcer[___]->tarcer,tarcer]>1,

(* generate a list of momentum pairs with one momentum belong to one 2-loop and another one belong to another 2-loop *)
		twoloopm=Replace[null tmp2,Except[tarcer[___]]->1,{1}]/.tarcer[ll1_,ll2_]:>tarcer[ll2[[;;2]]];
		twoloopm=(twoloopm2@@DeleteCases[List@@(null twoloopm),null])/.tarcer[aa_]:>aa;
		twoloopm=(twoloopm//.twoloopm2[{aa_,bb_},ll__]:>twoloopm2[aa,ll]twoloopm2[bb,ll]twoloopm2[ll])/.twoloopm2[{_,_}]->1;
		twoloopm=twoloopm//.twoloopm2[aa_,{bb_,cc_},ll__]:>twoloopm2[aa,bb]twoloopm2[aa,cc]twoloopm2[aa,ll];
		twoloopm=(List@@(twoloopm/.twoloopm2[aa_,{bb_,cc_}]:>twoloopm2[aa,bb]twoloopm2[aa,cc]))/.twoloopm2->List;


(* if exist SPD[p_a,p_b] that p_a belong to one of 2-loop while p_b belong to other 2-loop, then expand it *)
		numerator=numerator/.{Power[Pair[Momentum[aa_,dim___],Momentum[bb_,dim___]],power_]:>(twoloopm2=((!FreeQ[aa,#[[1]]]&&!FreeQ[bb,#[[2]]])||(!FreeQ[aa,#[[2]]]&&!FreeQ[bb,#[[1]]])&/@twoloopm)//Boole;
								If[!FreeQ[twoloopm2,1],
								QExpand[Pair[Momentum[aa,dim],Momentum[bb,dim]]^power,twoloopm[[Position[twoloopm2,1][[1,1]] ]] ],Pair[Momentum[aa,dim],Momentum[bb,dim]]^power]),
							Pair[Momentum[aa_,dim___],Momentum[bb_,dim___]]:>(twoloopm2=((!FreeQ[aa,#[[1]]]&&!FreeQ[bb,#[[2]]])||(!FreeQ[aa,#[[2]]]&&!FreeQ[bb,#[[1]]])&/@twoloopm)//Boole;
								If[!FreeQ[twoloopm2,1],
								QExpand[Pair[Momentum[aa,dim],Momentum[bb,dim]],twoloopm[[Position[twoloopm2,1][[1,1]] ]] ],Pair[Momentum[aa,dim],Momentum[bb,dim]]])};
							
		numerator=numerator//.Pair[Momentum[aa_+bb_,dim___],cc_]/;Or@@((!FreeQ[aa,#[[1]]]&&!FreeQ[bb,#[[2]]])&/@twoloopm):>(Pair[Momentum[aa,dim],cc]+Pair[Momentum[bb,dim],cc]);

	];
	
	


(**---------------------------------------------------------------------------**)
(**-------  collcet the momentum in 2-loop  ------**)

	tmp2=Expand[numerator tmp2/.tarcer[ll1_,ll2_]:>tarcer[null,ll1,ll2]];

	tmp2=tmp2//.{ Pair[Momentum[aa_,dim___],Momentum[bb_,dim___]]tarcer[ll0_,ll1_,ll2_]/;(!FreeQ[aa,ll2[[1]]|ll2[[2]]]||!FreeQ[bb,ll2[[1]]|ll2[[2]]]):>tarcer[ll0 Pair[Momentum[aa,dim],Momentum[bb,dim]],ll1,ll2],
				Pair[Momentum[aa_,dim___],bb_]tarcer[ll0_,ll1_,ll2_]/;!FreeQ[aa,ll2[[1]]|ll2[[2]]]:>tarcer[Pair[Momentum[aa,dim],bb]ll0,ll1,ll2],
				Power[Pair[Momentum[aa_,dim___],Momentum[bb_,dim___]],power_]tarcer[ll0_,ll1_,ll2_]/;(!FreeQ[aa,ll2[[1]]|ll2[[2]]]||!FreeQ[bb,ll2[[1]]|ll2[[2]]]):>tarcer[ll0 Pair[Momentum[aa,dim],Momentum[bb,dim]]^power,ll1,ll2],
				Power[Pair[Momentum[aa_,dim___],bb_],power_]tarcer[ll0_,ll1_,ll2_]/;!FreeQ[aa,ll2[[1]]|ll2[[2]]]:>tarcer[Pair[Momentum[aa,dim],bb]^power ll0,ll1,ll2]};



(**--- try convert the numerator to TARCER notation ---**)
(* shift or rescale the momentum in numerators *)
	tmp2=tmp2/.tarcer[ll0_,ll1_,ll2_]:>tarcer[If[Length[ll2[[4]] ]==3,ll0/.ll2[[4,1]]/.ll2[[4,2]]/.ll2[[4,3]],ll0/.ll2[[4,1]]/.ll2[[4,2]]],ll1,ll2];


	tmp22=tmp2/.tarcer[ll0_,ll1_,ll2_]:>tarcer[ll0/.{Power[Pair[Momentum[ll2[[1]],dim___],Momentum[aa_,dim___]],power_]/;NumericQ[Simplify[aa/ll2[[3]]]]:>Simplify[aa/ll2[[3]]]^power tnumerator[0,0,power,0,0],
											Pair[Momentum[ll2[[1]],dim___],Momentum[aa_,dim___]]/;NumericQ[Simplify[aa/ll2[[3]]]]:>Simplify[aa/ll2[[3]]] tnumerator[0,0,1,0,0],
											Power[Pair[Momentum[ll2[[2]],dim___],Momentum[aa_,dim___]],power_]/;NumericQ[Simplify[aa/ll2[[3]]]]:>Simplify[aa/ll2[[3]]]^power tnumerator[0,0,0,power,0],
											Pair[Momentum[ll2[[2]],dim___],Momentum[aa_,dim___]]/;NumericQ[Simplify[aa/ll2[[3]]]]:>Simplify[aa/ll2[[3]]] tnumerator[0,0,0,1,0],
											Power[Pair[Momentum[ll2[[1]],dim___],Momentum[ll2[[2]],dim___]],power_]:> tnumerator[0,0,0,0,power],
											Pair[Momentum[ll2[[1]],dim___],Momentum[ll2[[2]],dim___]]:> tnumerator[0,0,0,0,1]},ll1,ll2];


	tmp22=tmp22/.tarcer[ll0_,ll1_,ll2_]:>tarcer[ll0//.tnumerator[aa___]tnumerator[bb___]:>tnumerator@@({aa}+{bb}),ll1,ll2];


(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)
(*-------- if more terms are generated after expand the numerator, try reduce the integral for each term; TID for each 2-loop integral is neeeded usually --------*)
(**----- if not all numerators are successfully convert to TERCER notation, then exist, e.g. tarcer[FVD[k1,u],{...},{k1,...}], TID for each 2-loop integral -----**)

	If[!FreeQ[tmp22,tarcer[ll0_,ll1_,ll2_]/;!FreeQ[ll0,ll2[[1]]|ll2[[2]] ] ]||(ToString[Head[tmp22]]=="Plus"),

		If[steps=="true",
			If[ToString[Head[tmp22]]=="Plus",Print["Expand and check reducibility for each term..."]];
			Print["Doing tensor reduction..."]
		];
	
		tmp2=tmp2/.tarcer[ll0_,ll1_,ll2_]:>tarcer[Expand[QExpand[ll0(*/.null->1*),ll2[[;;2]]]/.Pair[Momentum[aa___Plus,dim___],LorentzIndex[bb_,dim___]]:>(Pair[Momentum[#,dim],LorentzIndex[bb,dim]]&/@Plus[aa])] ,ll1,ll2];
	(* ll0/.null->1 is because /.null->0 in QExpand[] effect the null here *)(* (p+q)^u -> p^u + q^u *)
	
		tmp2=tmp2/.tarcer[ll0_,ll1_,ll2_]:>tarcer[tarcer2[null]ll0/.Power[Pair[Momentum[aa_,dim___],LorentzIndex[ll_,dim___]],2]:>Pair[Momentum[aa,dim],Momentum[aa,dim]],ll1,ll2];
		tmp2=tmp2/.tarcer[ll0_,ll1_,ll2_]:>tarcer[Expand[ll0]//.tarcer2[aa_]Pair[Momentum[bb_,dim___],ll_]/;!FreeQ[bb,ll2[[1]]|ll2[[2]]]:>tarcer2[aa Pair[Momentum[bb,dim],ll]],ll1,ll2];
		(* Expand momentum; collect SPD[] & FVD[] that involve k1 or k2 to tarcer2[]*)


		tmp2=tmp2/.tarcer[ll0_,ll1_,ll2_]:>tarcer[ll0/.tarcer2[aa_]:>(pp=$AM[Unique[]];tarcer2[FCMultiLoopTID[ aa *
					FAD[{ll2[[1]],0,ll1[[1]]},{ll2[[2]],0,ll1[[2]]},{ll2[[1]]-pp,0,ll1[[3]]},{ll2[[2]]-pp,0,ll1[[4]]},{ll2[[1]]-ll2[[2]],0,ll1[[5]]}],ll2[[;;2]]],pp->ll2[[3]]]),ll1,ll2];

(* TID; the ll2[[3]] may have form p+q, so replace it by pp and pp -> p+q later; collect terms with same Lorentz structure *)
		tmp2=tmp2/.tarcer[ll0_,ll1_,ll2_]:>tarcer[Expand[ll0]/.{aa_ tarcer2[bb_,cc_]:>(Contract[aa bb]/.cc), tarcer2[bb_,cc_]:>( bb/.cc)},ll1,ll2];
		tmp2=tmp2/.tarcer[ll0_,ll1_,ll2_]:>tarcer[QSimplify2[ll0/.null->1],ll1,ll2];


(**-------------------------------------------------------------------------------------------------------------------------------------**)
(**------------------------- expand and try reduce the integral for each term -----------------------------**)
(* recover mom0 to FAD[] *)
		tmp=DeleteCases[tmp,0];

		If[Length[tmp]>0,
			tmp=Times@@(tmp/.mom0[aa_,bb_,cc_]:>(bb^2 Pair[Momentum[aa,D],Momentum[aa,D]])^(-cc))
			(*tmp=Transpose[tmp/.mom0[aa_,bb_,cc_]:>{aa,bb,cc}];
			tmp=1/(Times@@tmp[[2]])FAD@@Transpose[{tmp[[1]],Table[0,Length[tmp[[1]]] ],tmp[[3]]}]*)
		,
			tmp=1
		];



(**-----------------------------------------------**)
		(* TryReduce for each term *)
		tmp=DeleteCases[List@@(null0 + null0^2 + Expand[tmp tmp2/.{tarcer[ll0_,___]:>ll0,mom00[___]->1}]),null0|null0^2];

		(* give a list of results *)
		If[steps=="true",Print["Check reducibility for each term..."]];
		
		If[OptionValue[Contract]===True,
			
			{#[[1]],#[[2]],Contract[numerator2 #[[3]],ExpandScalarProduct->False]}&/@DeleteCases[TryReduce[#,mom]&/@tmp,0|{_,_,0}]
			(* It find that recover the numerator2 before TryReduce for each term make the evaluation very solw *)
		,
			{#[[1]],#[[2]],numerator2 #[[3]]}&/@DeleteCases[TryReduce[#,mom]&/@tmp,0|{_,_,0}]
		]

	,


(**-------------------------------------------------------------------------------------------------------------------------------------**)
(**-------------------------------------------------------------------------------------------------------------------------------------**)
(* if all numerators are successfully conver to TARCER notation *)
		tmp2=(tmp22/.null->1)/.{tarcer[ll0_,ll1_,ll2_]:>If[FreeQ[ll0,tnumerator],ll0 tarcer[{0,0,0,0,0},ll1,ll2],(ll0/.tnumerator[___]->1) tarcer[List@@(ll0/(ll0/.tnumerator[___]->1)),ll1,ll2]]};



(*------------------------------- try to reduce remaining 1-loop ----------------------------------*)
(**--- remove momentum already integrated ---**)
		mom1=If[FreeQ[tmp2,tarcer[ll0_,ll1_,ll2_]/;!FreeQ[ll2[[;;2]],#|-#]], #, 0]&/@mom1;
		mom1=DeleteCases[mom1,0];

(**--- update count & list ---**)
		tmp5=(Times@@DeleteCases[tmp,0])tmp2/.{tarcer[___]->1,mom00->mom0};
		tmp5=tmp5/.Power[mom0[aa_,bb_,cc_],power_]:>mom0[aa,bb^power,cc power];


		tmp5=List@@Replace[null tmp5,Except[mom0[___]]->1,{1}];

(* gather the equivalent momentum, e.g. 2k-q ~ k-q/2; counter the factor and exponent(mom0[[2]] and mom0[[3]]) *)
		tmp5=tmp5//.{ll0___,mom0[aa1_,aa2_,aa3_],ll1___,mom0[ bb1_,bb2_,bb3_],ll2___}/;NumberQ[Simplify[aa1/bb1 ] ]:>{ll0,mom0[aa1,aa2 bb2 Simplify[bb1/aa1]^(2bb3),aa3+bb3],ll1,ll2};
		tmp5=tmp5/.{mom0[aa_ bb_,cc_,dd_]/;NumericQ[aa]:>mom0[bb,cc aa^(2dd),dd],mom0[aa_  b1_+aa_ b2_,cc_,dd_]:>mom0[b1+b2,cc aa^(2dd),dd],mom0[aa_  b1_-aa_ b2_,cc_,dd_]:>mom0[b1-b2,cc aa^(2dd),dd]};
		tmp5=tmp5/.mom0[aa_,bb_,cc_]:>aa;(* only the momentums are needed *)

		count=Outer[!FreeQ[#1,#2|-#2]&,tmp5,mom1]//Boole//Transpose;
		list=(Plus@@#)&/@count;


		If[mom1=={},

			reducible=2;
			list1={1};

		,
		
(**---- if there remian loop momentum and no tadpole find at this stage, try reduce ---**)
			tadpole=!FreeQ[list,1];

(**------------------ reduce 1-loop ---------------------**)
(**---------- recursively find the momentum which only involved in 2 propagators --------**)

			If[tadpole,
				list1={mom1[[Position[list,1][[1,1]] ]],0};
				reducible=1
			,
				If[FreeQ[list,2],
					Print["Not a reducible diagram!"];
					reducible=0	
				,

			(***---------- check reducibility ----------***)
					While[(!FreeQ[list,2])&&(!tadpole),

			(***--- get the corresponding "external" momentum ---***)
						m=Position[list,2][[1,1]];
						mom2=mom1[[m]];
						list1=Append[list1,mom2];
						mom3=DeleteCases[tmp5 count[[m]],0];


			(***--- transform the loop to propagator, e.g. (k-p)(k-q) -> (p-q); update mom1, tmp, count, list, tadpole ---***)
						tmp5=tmp5/.{ll1___,mom3[[1]],ll2___,mom3[[2]],ll3___}:>{ll1,ll2,ll3,
									(mom3/.{aa_ mom2+bb_:>mom2+bb/aa,aa_ mom2:>mom2,- mom2+bb_:>mom2-bb,-mom2:>mom2})/.{cc_,dd_}:>cc-dd};

						mom1=Delete[mom1,m];
						tmp5=tmp5//.{ll1___,aa_,ll2___,bb_,ll3___}/;NumericQ[Simplify[aa/bb]]:>{ll1,aa,ll2,ll3};
						count=Outer[!FreeQ[#1,#2|-#2]&,tmp5,mom1]//Boole//Transpose;
						list=Count[#,1]&/@count;
						tadpole=!FreeQ[list,1];

					];


					If[(mom1=!={})&&(!tadpole),Print["Not a reducible diagram!"];reducible=0];
		
					If[tadpole,list1=Append[list1,0];reducible=1];
		
				];
			];

		];



(*-------------------------------  give the result -------------------------------------*)
(* recover mom0 to FAD[] *)
		tmp=DeleteCases[tmp,0];

		If[Length[tmp]>0,
			tmp=Times@@(tmp/.mom0[aa_,bb_,cc_]:>(bb^2 Pair[Momentum[aa,D],Momentum[aa,D]])^(-cc))
			(*tmp=Transpose[tmp/.mom0[aa_,bb_,cc_]:>{aa,bb,cc}];
			tmp=1/(Times@@tmp[[2]])FAD@@Transpose[{tmp[[1]],Table[0,Length[tmp[[1]]] ],tmp[[3]]}]*)
		,
			tmp=1
		];


		If[reducible==1&&!FreeQ[tmp2,tarcer],reducible=2];



(*-----------------------------*)
		tmp={reducible,
			list1,
			(* recover the numerator and Contract terms like y^u p_u *)
			If[OptionValue[Contract]===True,
				Contract[numerator2 tmp tmp2,ExpandScalarProduct->False]/.{mom00[___]->1,qfact2[aa_]:>qfact2[Simplify[aa]]}
			,
				(numerator2 tmp tmp2//.{Pair[Momentum[aa_,dim___],LorentzIndex[lo_,dim___]]bb_/;!FreeQ[bb,DiracGamma[LorentzIndex[lo,dim],dim]]:>
							(bb/.DiracGamma[LorentzIndex[lo,dim],dim]->DiracGamma[Momentum[aa,dim],dim]),
							Pair[LorentzIndex[lo1_,dim___],LorentzIndex[lo2_,dim___]]bb_/;!FreeQ[bb,DiracGamma[LorentzIndex[lo1,dim],dim]]&&!FreeQ[bb,DiracGamma[LorentzIndex[lo2,dim],dim]]:>
							(bb/.LorentzIndex[lo2,dim]->LorentzIndex[lo1,dim])})/.
							{Pair[Momentum[aa1_,dim___],LorentzIndex[lo_,dim___]]Pair[Momentum[aa2_,dim___],LorentzIndex[lo_,dim___]]:>Pair[Momentum[aa1,dim],Momentum[aa2,dim]],
							Power[Pair[Momentum[aa1_,dim___],LorentzIndex[lo_,dim___]],2]:>Pair[Momentum[aa1,dim],Momentum[aa1,dim]]}/.{mom00[___]->1,qfact2[aa_]:>qfact2[Simplify[aa]]}
			]
			};
						

		(*-----------------------------*)
		If[e2loop=="true",
	(* evaluate the 2-loop *)
			tmp/.tarcer[ll0_,ll1_,ll2_]:>1/(4Pi)^D QTFI[D,(ll2[[3]]/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb})^2,ll0,ll1]
(* the TFI[] in TARCER have measure d^dk with an overall factor 1/Pi^d ; while each loop momentum have meausure d^dk/(2Pi)^d ; times 1/(4Pi)^d to make d^dk=d^dk *)
		,
	(* show the 2-loop as qTFI or Tarcer`TFI *)
			If[totfi=="false",
			
				If[jacobi=!=1,
						tmp/.tarcer[cc1_,cc2_,cc3_]:>1/(4Pi)^D qTFI[cc1,cc1,{cc3[[1]],cc3[[2]],cc3[[3]],Append[cc3[[4]],"Jacobi"->jacobi]}],
						tmp/.tarcer[cc___]:>1/(4Pi)^D qTFI[cc]
					]

			,
	
				tmp/.tarcer[{0,0,0,0,0},ll1_,ll2_]:>1/(4Pi)^D Tarcer`TFI[D,(ll2[[3]]/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb})^2,ll1]/.
						tarcer[ll0_,ll1_,ll2_]:>1/(4Pi)^D Tarcer`TFI[D,(ll2[[3]]/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb})^2,ll0,ll1]
			]
		]
	]


]


]







End[]
