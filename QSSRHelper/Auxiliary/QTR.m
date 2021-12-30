(* Wolfram Language package *)

(* Author: ShungHong Li *)







QTR::usage =
	"QTR[expr_] evaluate the TR of a in a_ qfact1, which short the time of evaluation"	





Begin["`Private`QTR`"]



Options[QTR] = {
	Expandby->qfact1}







QTR[expr_,OptionsPattern[]]:=Block[{tmp,list,null,qqfact1,dot,expand=ToString[OptionValue[Expandby]]//ToLowerCase},

tmp=expr//FCI;

(*parallelize evaluate *)
If[expand=="all",

	tmp=List@@Expand[QExpand2[tmp]+ null+ null qfact1[null]];
	tmp=ParallelMap[TR,tmp]//Total
,
	
	If[expand=="dirac",
		(* gather by \[Gamma] structure*)
		tmp=QExpand2[tmp]/.Dot->dot;
		tmp=List@@Collect[tmp,dot[___]];

		tmp=Partition[tmp,UpTo[Quotient[Length[tmp],4$KernelCount]+1]];
		tmp=((Plus@@#)&/@tmp)/.dot->Dot;

		tmp=ParallelMap[TR,tmp]//Total
		
	,

    (* gather by qfact1 *)
		tmp=List@@Collect[(expr//FCI)+ null+ null qfact1[null],qfact1[___]];
		
		tmp=ParallelMap[Replace[#,{aa_ bb__qfact1 Power[qfact1[cc_],dd_]:>TR[aa//Expand](Times[bb]/.qfact1->qqfact1)Power[qqfact1[cc],dd]//Expand , aa_ Power[qfact1[cc_],dd_]:>TR[aa//Expand]Power[qqfact1[cc],dd]//Expand,
						 aa_ bb__qfact1:>TR[aa//Expand](Times[bb]/.qfact1->qqfact1)//Expand},{0}]&,tmp];
		list=(FreeQ[#,qqfact1]&/@tmp)/.{False->0,True->1};(* the term not matched with above *)

		tmp=TR[(list tmp)//Total]+Total[(1-list)tmp];
	];
];

tmp/.{null->0,qqfact1->qfact1}
]




End[]