(* Wolfram Language package *)


QContract::usage =
	"QContract[expr_] Contract terms not in qfact1[], which short the time of evaluation"


Begin["`Private`QContract`"]


QContract[expr_]:=Block[{tmp,list,null,qqfact1},

tmp=List@@Collect[(expr//FCI)+ null+ null qfact1[null],qfact1[___]];

tmp=ParallelMap[Replace[#,{aa_ bb__qfact1 Power[qfact1[cc_],dd_]:>Contract[aa//Expand](Times[bb]/.qfact1->qqfact1)Power[qqfact1[cc],dd]//Expand , 
					aa_ Power[qfact1[cc_],dd_]:>Contract[aa//Expand]Power[qqfact1[cc],dd]//Expand, aa_ bb__qfact1:>Contract[aa//Expand](Times[bb]/.qfact1->qqfact1)//Expand},{0}]&,tmp];

list=(FreeQ[#,qqfact1]&/@tmp)/.{False->0,True->1};(* the term not matched *)

tmp=Contract[(list tmp)//Total]+Total[(1-list)tmp];

tmp/.{null->0,qqfact1->qfact1}
]


End[]