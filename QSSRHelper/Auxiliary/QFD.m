(* Wolfram Language package *)


QFD::usage =
	"qFD[expr_,p_] evaluate the FourDivergence on a in a_ qfact1, which short the time of evaluation"	


Begin["`Private`QFD`"]




QFD[expr_,p_]:=Block[{tmp,list,null,qqfact1,pp=Cases[p//FCI,Momentum[xx_,___]:>xx,Infinity][[1]]},

tmp=List@@Collect[(expr//FCI)+ null+ null qfact1[null],qfact1[___]];

tmp=ParallelMap[Replace[#,{aa_ bb__qfact1 Power[qfact1[cc_],dd_]:>FourDivergence[QExpand[aa//Expand,pp],p](Times[bb]/.qfact1->qqfact1)Power[qqfact1[cc],dd]//Expand ,
						 aa_ Power[qfact1[cc_],dd_]:>FourDivergence[QExpand[aa//Expand,pp],p]Power[qqfact1[cc],dd]//Expand,
						 aa_ bb__qfact1:>FourDivergence[QExpand[aa//Expand,pp],p](Times[bb]/.qfact1->qqfact1)//Expand},{0}]&,tmp];
list=(FreeQ[#,qqfact1]&/@tmp)/.{False->0,True->1};(* the term not matched *)

tmp=FourDivergence[QExpand[(list tmp)//Total,pp],p]+Total[(1-list)tmp];

tmp/.{null->0,qqfact1->qfact1}
]








End[]
