(* ::Package:: *)

(* Wolfram Language package *)

(* Author: ShungHong Li *)




QExpand2::usage = 
	"QExpand2[expr_] extract gamma matrices from terms mixed with commutative and noncommutative terms"	
QExpand2::warn="Non-commutative object involved in commutative product!"




Begin["`Private`QExpand2`"]

Options[QExpand2] = {
	NonCommutative->{}}



(*-----------------------------------------------------------------*)
QExpand2[expr_,OptionsPattern[]]:=Block[{tmp,dot,times,plus,nonc},
tmp=expr//FCI;

(* expand terms in the dot product *)
(*tmp=Expand[tmp/.DiracSigma[aa_,bb_]:>I/2(aa . bb-bb . aa)]/.Dot->dot;*)
tmp=Expand[tmp]/.Dot->dot;
tmp=tmp/.dot[aa_]:>dot[aa/.bb_Times:>Expand[bb]];


(*tmp=DiracGammaExpand[tmp];*)
(*tmp=tmp/.{qfact1[a_]:>qfact1[a/.{Times->times,Plus->plus}],Power[a_,b_]:>(Power[a,b]/.{Times->times,Plus->plus}),qGamma[a_]:>qGamma[a/.{Times->times,Plus->plus}],Gamma[a_]:>Gamma[a/.{Times->times,Plus->plus}]};*)
tmp=tmp/.{Plus->plus,Times->times};



(* -------------- expand until no nest of dot ------------- *)
tmp=tmp//.{dot[a___,plus[b___],d___]:>plus@@(dot[a,#,d]&/@{b}),times[a___,plus[b___],d___]:>plus@@(times[a,#,d]&/@{b})};
tmp=tmp//.dot[aa___,dot[bb__],cc___]:>dot[aa,bb,cc];


(* e.g. y^e.(T^a.T^b * y^c.y^d) - > y^e.T^a.T^b.y^c.y^d *)
tmp=tmp//.dot[aa___,times[bb1___,bb2_dot,bb3___,bb4_dot,bb5___],cc___]/;
		((FreeQ[bb2,DiracGamma|DiracSigma]&&!FreeQ[bb2,SUNT]&&FreeQ[bb4,SUNT]&&!FreeQ[bb4,DiracGamma|DiracSigma])||
		(FreeQ[bb4,DiracGamma|DiracSigma]&&!FreeQ[bb4,SUNT]&&FreeQ[bb2,SUNT]&&!FreeQ[bb2,DiracGamma|DiracSigma])):>dot[aa,bb1,bb2,bb3,bb4,bb5,cc];
		
tmp=tmp//.{dot[aa___,times[bb1___,bb2_dot,bb3___,bb4_DiracGamma,bb5___],cc___]/;(FreeQ[bb2,DiracGamma|DiracSigma]&&!FreeQ[bb2,SUNT]):>dot[aa,bb1,bb2,bb3,bb4,bb5,cc],
			dot[aa___,times[bb1___,bb2_dot,bb3___,bb4_DiracSigma,bb5___],cc___]/;(FreeQ[bb2,DiracGamma|DiracSigma]&&!FreeQ[bb2,SUNT]):>dot[aa,bb1,bb2,bb3,bb4,bb5,cc],
			dot[aa___,times[bb1___,bb2_DiracGamma,bb3___,bb4_dot,bb5___],cc___]/;(FreeQ[bb4,DiracGamma|DiracSigma]&&!FreeQ[bb4,SUNT]):>dot[aa,bb1,bb2,bb3,bb4,bb5,cc],
			dot[aa___,times[bb1___,bb2_DiracSigma,bb3___,bb4_dot,bb5___],cc___]/;(FreeQ[bb4,DiracGamma|DiracSigma]&&!FreeQ[bb4,SUNT]):>dot[aa,bb1,bb2,bb3,bb4,bb5,cc],
			dot[aa___,times[bb1___,bb2_SUNT,bb3___,bb4_dot,bb5___],cc___]/;(!FreeQ[bb4,DiracGamma|DiracSigma]&&FreeQ[bb4,SUNT]):>dot[aa,bb1,bb2,bb3,bb4,bb5,cc],
			dot[aa___,times[bb1___,bb2_dot,bb3___,bb4_SUNT,bb5___],cc___]/;(!FreeQ[bb2,DiracGamma|DiracSigma]&&FreeQ[bb2,SUNT]):>dot[aa,bb1,bb2,bb3,bb4,bb5,cc]};

tmp=tmp//.{dot[aa___,times[bb1___,bb2_SUNT,bb3___,bb4_DiracGamma,bb5___],cc___]:>dot[aa,bb1,bb2,bb3,bb4,bb5,cc],
			dot[aa___,times[bb1___,bb2_SUNT,bb3___,bb4_DiracSigma,bb5___],cc___]:>dot[aa,bb1,bb2,bb3,bb4,bb5,cc],
			dot[aa___,times[bb1___,bb2__DiracGamma,bb3___,bb4_SUNT,bb5___],cc___]:>dot[aa,bb1,bb2,bb3,bb4,bb5,cc],
			dot[aa___,times[bb1___,bb2__DiracSigma,bb3___,bb4_SUNT,bb5___],cc___]:>dot[aa,bb1,bb2,bb3,bb4,bb5,cc]};

(*
tmp=tmp//.{dot[a___,plus[b___],d___]:>plus@@(dot[a,#,d]&/@{b}),times[a___,plus[b___],d___]:>plus@@(times[a,#,d]&/@{b}),
			times[a___,times[b___],c___]:>times[a,b,c],
			dot[a___,times[b___,dot[c___],e___],d___]:>times[dot[a,c,d],b,e],dot[a___,dot[c___],d___]:>dot[a,c,d]};
*)
			
tmp=tmp/.{dot[a___,0,b___]->0};						
(*	
(* -----------it's still possible have terms like dot[a___,b(c+d),e___]----------- *)																							
tmp=tmp/.dot[aa___]:>dot@@({aa}//.times[a___,plus[b___],c___]:>plus@@(times[a,#,c]&/@{b}));
tmp=tmp//.dot[a___,plus[b___],d___]:>plus@@(dot[a,#,d]&/@{b});


tmp=tmp//.{dot[a___,times[b___,SUNT[su_],bb___],c___]:>times[b,bb] dot[a,SUNT[su],c],dot[a___,times[b___,DiracGamma[dg_,dd___],bb___],c___]:>times[b,bb] dot[a,DiracGamma[dg,dd],c]};
(*---------- no non-commutative object in dot[times[]] now ------------------*)
tmp=tmp//.dot[a___,times[b___],c___]:>times[b] dot[a,c];

tmp=tmp//.{dot[a___,nn_Integer,b___]:>nn dot[a,b],dot[a___,nn_Rational,b___]:>nn dot[a,b]};
*)


If[ListQ[OptionValue[NonCommutative]],nonc=Join[OptionValue[NonCommutative],{DiracGamma,DiracSigma,SUNT}]//DeleteDuplicates,nonc={DiracGamma,DiracSigma,SUNT}];



tmp=tmp//.dot[aa___,bb_ cc_,dd___]/;FreeQ[cc,Alternatives@@nonc]:>cc dot[aa,bb,dd];
tmp=tmp//.dot[aa___,bb_ ,dd___]/;FreeQ[bb,Alternatives@@nonc]:>bb dot[aa,dd];

tmp=tmp/.times->Times;
If[!FreeQ[tmp,dot[a___]dot[b___]],Message[qExpand2::warn]];

Expand[tmp]/.plus->Plus/.dot->Dot

]



(*-----------------------------------------------------------------*)

End[]
