(* Wolfram Language package *)

QExpand2::usage = 
	"QExpand2[expr_] extract gamma matrices from terms mixed with commutative and noncommutative terms"	

Begin["`Private`QExpand2`"]

(*-----------------------------------------------------------------*)
QExpand2[expr_]:=Block[{tmp,dot,times,plus},
tmp=expr//FCI;

tmp=Expand[tmp/.DiracSigma[aa_,bb_]:>I/2(aa . bb-bb . aa)]/.Dot->dot;
(*tmp=DiracGammaExpand[tmp];*)

tmp=tmp/.{qfact1[a_]:>qfact1[a/.{Times->times,Plus->plus}],Power[a_,b_]:>(Power[a,b]/.{Times->times,Plus->plus}),Qamm[a_]:>Qamm[a/.{Times->times,Plus->plus}],Gamma[a_]:>Gamma[a/.{Times->times,Plus->plus}]};
tmp=tmp/.{Plus->plus,Times->times};



(* -------------- expand until no nest of dot ------------- *)
tmp=tmp//.{dot[a___,plus[b___],d___]:>plus@@(dot[a,#,d]&/@{b}),times[a___,plus[b___],d___]:>plus@@(times[a,#,d]&/@{b}),
			times[a___,times[b___],c___]:>times[a,b,c],
			dot[a___,times[b___,dot[c___],e___],d___]:>times[dot[a,c,d],b,e],dot[a___,dot[c___],d___]:>dot[a,c,d]};

			
tmp=tmp/.{dot[a___,0,b___]->0};						
	
(* -----------it's still possible have terms like dot[a___,b(c+d),e___]----------- *)																							
tmp=tmp/.dot[aa___]:>dot@@({aa}//.times[a___,plus[b___],c___]:>plus@@(times[a,#,c]&/@{b}));
tmp=tmp//.dot[a___,plus[b___],d___]:>plus@@(dot[a,#,d]&/@{b});


tmp=tmp//.{dot[a___,times[b___,SUNT[su_],bb___],c___]:>times[b,bb] dot[a,SUNT[su],c],dot[a___,times[b___,DiracGamma[dg_,dd___],bb___],c___]:>times[b,bb] dot[a,DiracGamma[dg,dd],c]};
(*---------- no non-commutative object in dot[times[]] now ------------------*)
tmp=tmp//.dot[a___,times[b___],c___]:>times[b] dot[a,c];

tmp=tmp//.{dot[a___,nn_Integer,b___]:>nn dot[a,b],dot[a___,nn_Rational,b___]:>nn dot[a,b]};

If[!FreeQ[tmp,dot[a___]dot[b___]],Print["Non-commutative terms involved in commutative Times[], make sure the input is correct!"]];

Expand[tmp]/.{times->Times,plus->Plus,dot->Dot,plus->Plus,times->Times}
]



(*-----------------------------------------------------------------*)

End[]