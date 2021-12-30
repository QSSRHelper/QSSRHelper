(* Wolfram Language package *)

QTV::usage= "QTV[dim_,p_,{v5_Integer,v2_Integer,v3_Integer,v4_Integer}] evaluate the TVI give the result as a propagatr ~ (p^2)^..."

Begin["`Private`QTV`"]


QTV[dim_,mom_,{{v5_Integer,0},{v2_Integer,0},{v3_Integer,0},{v4_Integer,0}}]:=QTV[dim,mom,{v5,v2,v3,v4}]

QTV[dim_,mom_,{v5_Integer,v2_Integer,v3_Integer,v4_Integer}]:=Module[{k1,k2,pp,p},

p=Factor[mom]/.Power[a_,2]:>(a/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb});


(* d^Dk/(2Pi)^D for each loop; TARCER has only an overall factor 1/Pi^D ; there is a prefactor 1/(4Pi)^D for each TFI when doing TryReduce[]. times (2Pi)^D/Pi^D to make d^Dk=d^Dk *)
IntegrateP[(4Pi)^(dim) FeynAmpDenominator@@Flatten[{Table[PropagatorDenominator[Momentum[k1-k2,dim],0],v5],Table[PropagatorDenominator[Momentum[k2,dim],0],v2],
		Table[PropagatorDenominator[Momentum[k1-pp,dim],0],v3],Table[PropagatorDenominator[Momentum[k2-pp,dim],0],v4]}] ,k1,k2]/.pp->p

]





End[]