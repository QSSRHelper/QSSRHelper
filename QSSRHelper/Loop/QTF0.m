(* Wolfram Language package *)

QTF0::usage= "QTF0[dim_,p_,uvrst___List,{v1_Integer,v2_Integer,v3_Integer,v4_Integer,v5_Integer}] evaluate the TFI with at least one of v1,v2,v3,v4,v5 = 0, and give the result as a propagatr ~ (p^2)^..."


Begin["`Private`QTF0`"]




(* by expr, if QTF0[expr___] should be inteperated as QTFI[expr___], replace QTF0 to QTFI *)

QTF0[dim_,mom_,{u_Integer,v_Integer,r_Integer,s_Integer,t_Integer},{v1_Integer,v2_Integer,v3_Integer,v4_Integer,v5_Integer}]/;FreeQ[{v1,v2,v3,v4,v5},0]:=QTFI[Tarcer`TFI[dim,mom,{u,v,r,s,t},{v1,v2,v3,v4,v5}]]
QTF0[dim_,mom_,{u_Integer,v_Integer,r_Integer,s_Integer,t_Integer},{{v1_Integer,0},{v2_Integer,0},{v3_Integer,0},{v4_Integer,0},{v5_Integer,0}}]/;FreeQ[{v1,v2,v3,v4,v5},0]:=QTFI[Tarcer`TFI[dim,mom,{u,v,r,s,t},{v1,v2,v3,v4,v5}]]

QTF0[dim_,mom_,{v1_Integer,v2_Integer,v3_Integer,v4_Integer,v5_Integer}]/;FreeQ[{v1,v2,v3,v4,v5},0]:=QTFI[Tarcer`TFI[dim,mom,{v1,v2,v3,v4,v5}]]
QTF0[dim_,mom_,{{v1_Integer,0},{v2_Integer,0},{v3_Integer,0},{v4_Integer,0},{v5_Integer,0}}]/;FreeQ[{v1,v2,v3,v4,v5},0]:=QTFI[Tarcer`TFI[dim,mom,{v1,v2,v3,v4,v5}]]




QTF0[dim_,mom_,{u_Integer,v_Integer,r_Integer,s_Integer,t_Integer},{v1_Integer,v2_Integer,v3_Integer,v4_Integer,v5_Integer}]/;!FreeQ[{v1,v2,v3,v4,v5},0]:=qTF0[dim,mom,{u,v,r,s,t},{v1,v2,v3,v4,v5}]
QTF0[dim_,mom_,{u_Integer,v_Integer,r_Integer,s_Integer,t_Integer},{{v1_Integer,0},{v2_Integer,0},{v3_Integer,0},{v4_Integer,0},{v5_Integer,0}}]/;!FreeQ[{v1,v2,v3,v4,v5},0]:=qTF0[dim,mom,{u,v,r,s,t},{v1,v2,v3,v4,v5}]

QTF0[dim_,mom_,{v1_Integer,v2_Integer,v3_Integer,v4_Integer,v5_Integer}]/;!FreeQ[{v1,v2,v3,v4,v5},0]:=qTF0[dim,mom,{0,0,0,0,0},{v1,v2,v3,v4,v5}]
QTF0[dim_,mom_,{{v1_Integer,0},{v2_Integer,0},{v3_Integer,0},{v4_Integer,0},{v5_Integer,0}}]/;!FreeQ[{v1,v2,v3,v4,v5},0]:=qTF0[dim,mom,{0,0,0,0,0},{v1,v2,v3,v4,v5}]





(*-----------------------------*)

qTF0[dim_,mom_,{u_Integer,v_Integer,r_Integer,s_Integer,t_Integer},{v1_Integer,v2_Integer,v3_Integer,v4_Integer,v5_Integer}]/;!FreeQ[{v1,v2,v3,v4,v5},0]:=Module[{tmp,k1,k2,pp,p},

p=Factor[mom]/.Power[a_,2]:>(a/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb});

tmp=FeynAmpDenominator@@Flatten[{Table[PropagatorDenominator[Momentum[k1,dim],0],v1],Table[PropagatorDenominator[Momentum[k2,dim],0],v2],Table[PropagatorDenominator[Momentum[k1-pp,dim],0],v3],
		Table[PropagatorDenominator[Momentum[k2-pp,dim],0],v4],Table[PropagatorDenominator[Momentum[k1-k2,dim],0],v5]}];


tmp=TryReduce[tmp,{k1,k2}];


If[!FreeQ[tmp[[2]],0],
(* if involve tadpole *)
	0
,

(* d^Dk/(2Pi)^D for each loop; TARCER has only an overall factor 1/Pi^D ; there is a prefactor 1/(4Pi)^D for each TFI when doing TryReduce[]. times (2Pi)^D/Pi^D to make d^Dk=d^Dk *)
	IntegrateP[(4Pi)^(dim) tmp[[3]] Pair[Momentum[k1,dim],Momentum[k1,dim]]^u Pair[Momentum[k2,dim],Momentum[k2,dim]]^v Pair[Momentum[k1,dim],Momentum[pp,dim]]^r*
			 Pair[Momentum[k2,dim],Momentum[pp,dim]]^s Pair[Momentum[k1,dim],Momentum[k2,dim]]^t,tmp[[2,1]],tmp[[2,2]]]/.pp->p
]


]















End[]