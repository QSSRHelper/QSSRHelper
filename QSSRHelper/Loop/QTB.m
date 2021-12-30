(* Wolfram Language package *)

QTB::usage= "QTB[dim_,p_,{v1_Integer,v3_Integer}] evaluate the TBI give the result as a propagatr ~ (p^2)^..."



Begin["`Private`QTB`"]






QTB[dim_,mom_,{{v1_Integer,0},{v3_Integer,0}}]:=QTB[dim,mom,{v1,v3}]

QTB[dim_,mom_,{v1_Integer,v3_Integer}]:=Module[{k1,pp,p},

p=Factor[mom]/.Power[a_,2]:>(a/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb});

(* d^Dk/(2Pi)^D for each loop; TARCER has only an overall factor 1/Pi^D ; there is a prefactor 1/(4Pi)^D for each TFI when doing TryReduce[]. 
	times (2Pi)^D/Pi^D to make d^Dk=d^Dk, note TFI ~ TBI^2 *)
IntegrateP[(4Pi)^(dim/2) FeynAmpDenominator@@Flatten[{Table[PropagatorDenominator[Momentum[k1,dim],0],v1],Table[PropagatorDenominator[Momentum[k1-pp,dim],0],v3]}] ,k1]/.pp->p
]







End[]