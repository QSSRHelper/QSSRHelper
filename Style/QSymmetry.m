(* Wolfram Language package *)

(* Author: ShungHong Li *)





QSymmetry::usage = 
	"QSymmetry[expr_,{indices__},Normalize->False] symmytrilize the expr by the indices"	
	
	
Begin["`Private`QSymmetry`"]


Options[QSymmetry] = {
	Normalize->False}



QSymmetry[expr_,symm_List,OptionsPattern[]]:=Block[{tmp,list,slist,asy,normal=OptionValue[Normalize]},
tmp=expr;

(* convention: {{u},{v},...} anti-symmetrlize; {u,v,...} symmtrilize *)
asy=Times@@Boole[MatchQ[#,_List]&/@symm];

If[asy==1,
	list=Transpose[symm][[1]];
,
	list=symm;
];


slist=Permutations[list];

(* (anti)symmtrize *)
If[asy==1,
	tmp=(Signature[#]tmp/.Thread[Rule[list,#]])&/@slist;
	
	If[ToLowerCase[ToString[normal]]=="true",
		tmp=1/Length[slist] Signature[slist[[1]]]tmp//Total
(* times Signature[slist[[1]]] so that the signature of expr it's self is positive *)
	,
		tmp=Signature[slist[[1]]]tmp//Total
	]
,
	If[ToLowerCase[ToString[normal]]=="true",
		tmp=1/Length[slist] Total[(tmp/.Thread[Rule[list,#]])&/@slist]
	,
		tmp=Total[(tmp/.Thread[Rule[list,#]])&/@slist]
	]
]

]


End[]