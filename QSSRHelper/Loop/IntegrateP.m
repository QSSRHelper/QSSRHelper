(* Wolfram Language package *)

(* Author: ShungHong Li *)





IntegrateP::usage =
	"IntegrateP[expr,p] is a simple feyman integral in momentum space for two feynman parameters"
	

Begin["`Private`IntegrateP`"]



Options[IntegrateP] = {
	Contract->False,
	lessdummy->True,
	Simplify->True,
	ShowSteps->False,
	ScaleMu->False}





IntegrateP[expr_,x_,y__/;FreeQ[{y},Rule],opts___Rule]:=IntegrateP[IntegrateP[expr,x,opts],y,opts]






(* if directely act IntegrateP[] on the output of TryReduce[] *)
IntegrateP[{nn_Integer/;nn>0,moms_List,expr_}]:=If[!FreeQ[moms,0],0,If[nn==2&&moms==={1},expr/.{Tarcer`TFI->QTFI,qTFI->QTFI},IntegrateP@@Prepend[moms,expr]]]
IntegrateP[expr_List/;And@@(MatchQ[#,{_Integer,_List,_}]&/@expr)]:=QSimplify2[Plus@@(IntegrateP[#]&/@(expr//.{ll0___,{n_,list_List,aa_},ll1___,{n_,list_List,bb_},ll2___}:>{ll0,{n,list,aa+bb},ll1,ll2}))]
IntegrateP[{0,moms_List,expr_}]:=(Print["Nonreducible integral!"];expr)



(*-----------------*)
IntegrateP[expr:Except[_List],{p_},opts___Rule]:=IntegrateP[expr,p,opts]





IntegrateP[expr:Except[_List],pp_List/;Length[pp]>1,opts___Rule]:=Module[{tmp,tmp0,tmp2,options={opts},steps=ToLowerCase[ToString[OptionValue[ShowSteps]]]},

tmp=expr//FCI;

(*--- if invole noncommutative product ---*)
If[!FreeQ[tmp,DiracTrace[a_]/;!FreeQ[a,DiracGamma[Momentum[aa_/;!And@@(FreeQ[aa,#]&/@pp),dim___],dim___]]],
	If[steps=="true",Print["Evaluate the DiracTrace..."]];
	tmp=tmp/.DiracTrace[aa_]:>DiracTrace[aa,DiracTraceEvaluate->True]
];


If[!FreeQ[tmp,DiracGamma[Momentum[aa_/;!And@@(FreeQ[aa,#]&/@pp),dim___],dim___]],
	If[steps=="true",Print["Uncontract GSD..."]];
	tmp=QExpand[tmp,pp]
];


tmp=tmp//Expand;

(*-----------------------------------------*)
(*
If[ToString[Head[tmp]]=="Plus",
(*--- if have more than on term ---*)
	IntegrateP[#,pp,opts]&/@tmp

,*)
	If[Or@@(FreeQ[tmp,#]&/@pp),
		Print["Check input!"];
		tmp

	,
(*--- try reduce the integral ---*)
		tmp=TryReduce[tmp,pp]//FCI;

(*--- if only one term after reduce ---*)
		If[MatchQ[tmp,{aa_Integer,bb_List,cc_}],

				If[tmp[[1]]==0,
					Print["Not a reducible integral!"];
					tmp[[3]]

				,
					If[!FreeQ[tmp[[2]],0],
						0
					,
					
					(* result *)
						If[steps=="true",Print["Integrate..."]];
						
						If[tmp[[1]]==2&&tmp[[2]]=={1},
						
							tmp[[3]]/.{Tarcer`TFI->QTFI,qTFI->QTFI}
						,
							IntegrateP@@Join[Prepend[tmp[[2]],tmp[[3]]/.{Tarcer`TFI->QTFI,qTFI->QTFI}],options]
						]
					]
				]

		,

(*--- if more than one term after reduce ---*)
			If[And@@(MatchQ[#,{aa_Integer,bb_List,cc_}]&/@tmp),

				tmp2=Select[tmp,MatchQ[#,{2,{1},cc_}]&];(* terms not involed 1-loop integral *)
				tmp2=If[tmp2=!={},Plus@@(Transpose[Select[tmp,MatchQ[#,{2,{1},cc_}]&]][[3]]),0];
				
				tmp0=Select[tmp,MatchQ[#,{0,bb_List,cc_}]&];(* terms invole nonreducible integral *)
				
				tmp=DeleteCases[tmp,{aa_,bb_List/;!FreeQ[bb,0],cc_}|{2,{1},cc_}|{0,bb_List,cc_}];
				
				If[Length[tmp0]>0,
					Print["Nonreducible integral involved, which will not be executed."];
					tmp0=Plus@@(#[[3]]&/@tmp0)
				];


				tmp=tmp/.{Tarcer`TFI->QTFI,qTFI->QTFI};
			
			(* gather terms with same list of momentum (same momentums and same order) *)
				tmp=tmp//.{ll0___,{n_,list_List,aa_},ll1___,{n_,list_List,bb_},ll2___}:>{ll0,{n,list,aa+bb},ll1,ll2};
			
				If[steps=="true",Print["Integrate ..."]];
				
			(* results *)
				tmp2=tmp2/.{Tarcer`TFI->QTFI,qTFI->QTFI};
				QSimplify2[Plus@@((IntegrateP@@Join[Prepend[#[[2]],#[[3]]],options])&/@tmp)+tmp2]+(Plus@@tmp0)

			]
		]

	]

(*]*)


]



(*------------------------------------------------------------------*)



IntegrateP[expr_,p_,OptionsPattern[]]:=Block[{tmp,dim,null,contract=OptionValue[Contract],less=OptionValue[lessdummy],simp=OptionValue[Simplify],smu=ToLowerCase[ToString[OptionValue[ScaleMu]]]},

If[smu=="true",
	tmp=ScaleMu^(4-D)IntegrateX[expr,p,Contract->OptionValue[Contract],dp->True,lessdummy->OptionValue[lessdummy],Simplify->OptionValue[Simplify]]
	,
	tmp=IntegrateX[expr,p,Contract->OptionValue[Contract],dp->True,lessdummy->OptionValue[lessdummy],Simplify->OptionValue[Simplify]]
]
]






End[]
