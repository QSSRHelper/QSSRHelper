(* Wolfram Language package *)



QTFI::usage="QTFI[expr_] is a function evaluate the TFI (give result as a proapgator) in expr."



Begin["`Private`QTFI`"]


QTFI[expr:Except[_Tarcer`TFI]]:=expr/.{qTFI[aa_Tarcer`TFI,_List]:>QTFI[aa],Tarcer`TFI[aa___]:>QTFI[Tarcer`TFI[aa]]}
QTFI[aa_Tarcer`TFI,_List]:=QTFI[aa]
QTFI[dim_,mom_,{u_Integer,v_Integer,r_Integer,s_Integer,t_Integer},{v1_Integer,v2_Integer,v3_Integer,v4_Integer,v5_Integer}]:=QTFI[Tarcer`TFI[dim,mom,{u,v,r,s,t},{v1,v2,v3,v4,v5}]]
QTFI[dim_,mom_,{u_Integer,v_Integer,r_Integer,s_Integer,t_Integer},{{v1_Integer,0},{v2_Integer,0},{v3_Integer,0},{v4_Integer,0},{v5_Integer,0}}]:=QTFI[Tarcer`TFI[dim,mom,{u,v,r,s,t},{v1,v2,v3,v4,v5}]]

QTFI[dim_,mom_,{v1_Integer,v2_Integer,v3_Integer,v4_Integer,v5_Integer}]:=QTFI[Tarcer`TFI[dim,mom,{v1,v2,v3,v4,v5}]]
QTFI[dim_,mom_,{{v1_Integer,0},{v2_Integer,0},{v3_Integer,0},{v4_Integer,0},{v5_Integer,0}}]:=QTFI[Tarcer`TFI[dim,mom,{v1,v2,v3,v4,v5}]]


(*--------------------------------------------*)

QTFI[expr_Tarcer`TFI]:=Module[{pp,rule},

pp=Factor[expr[[2]] ]/.Power[a_,2]:>(a/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb});

rule=pp->Pair[Momentum[pp,expr[[1]]],Momentum[pp,expr[[1]]]]^(1/2);

(* conver the momentum in TARCER to FeynCalc notation; Evaluate the TFI[], ... *)
Tarcer`TarcerRecurse[expr]/.{aa_ Tarcer`TVI[bb___]:>(aa/.rule)Tarcer`TVI[bb],aa_ Power[Tarcer`TVI[bb___],power_]:>(aa/.rule)Tarcer`TVI[bb]^power,
	aa_ Tarcer`TJI[bb___]:>(aa/.rule)Tarcer`TJI[bb],aa_ Power[Tarcer`TJI[bb___],power_]:>(aa/.rule)Tarcer`TJI[bb]^power,
	aa_ Tarcer`TBI[bb___]:>(aa/.rule)Tarcer`TBI[bb],aa_ Power[Tarcer`TBI[bb___],power_]:>(aa/.rule)Tarcer`TBI[bb]^power,
	aa_ Tarcer`TAI[bb___]:>(aa/.rule)Tarcer`TAI[bb],aa_ Power[Tarcer`TAI[bb___],power_]:>(aa/.rule)Tarcer`TAI[bb]^power,
	aa_ Tarcer`TFI[bb___]:>(aa/.rule)Tarcer`TFI[bb],aa_ Power[Tarcer`TFI[bb___],power_]:>(aa/.rule)Tarcer`TFI[bb]^power}/.{Tarcer`TVI->QTV,Tarcer`TJI->QTJ,Tarcer`TBI->QTB,Tarcer`TFI->QTF0}

]







End[]