(* Wolfram Language package *)

(* Author: ShungHong Li *)




Borel::usage = 
	"Borel[expr,{momentum,parameter}] is Borel transformation"




Begin["`Private`Borel`"]




Options[Borel] ={
	Derivate->0,
	Subtraction->0,
	Dispersion->True,
	Im->True}






Borel[expr_List,factor_List,OptionsPattern[]]:=
Block[
{tmp,tmpl,tmpr=0,i,deriv=OptionValue[Derivate],disp=OptionValue[Dispersion],sub=OptionValue[Subtraction],im=OptionValue[Im],fac=factor,s},
tmp=expr//FCI;

If[Length[tmp[[1]]]!=2,Print["check the input!"];Abort[]];

If[disp,

	s=If[Length[factor]!=3,Print["check the input!"];Abort[], factor[[3]]];

	For[i=1,i<Length[tmp]+1,i++,
	
		tmp[[i]]=Append[tmp[[i]],{}];
		tmp[[i,3]] = Borel[tmp[[i,2]],fac, Derivate->deriv,Dispersion->disp,Im->im,Subtraction->sub];

		tmp[[i,2]]= If[ sub>0,
			RowBox[{"\!\(\*FractionBox[\(1\), \(\[Pi]\)]\)",SubsuperscriptBox["\[Integral]","0","\[Infinity]"],"d",ToBoxes[s,TraditionalForm],FractionBox["1",If[sub>1,SuperscriptBox[ToString[s],ToString[sub]],ToString[s]] ]}],
			RowBox[{"\!\(\*FractionBox[\(1\), \(\[Pi]\)]\)",SubsuperscriptBox["\[Integral]","0","\[Infinity]"],"d",ToBoxes[s,TraditionalForm]}] 
			]//DisplayForm];
,

	For[i=1,i<Length[tmp]+1,i++,
		tmp[[i,2]] = Borel[tmp[[i,2]],fac, Derivate->deriv,Dispersion->disp,Im->im,Subtraction->sub]]
];

tmp
]




Borel[expr:Except[_?ListQ],factor_List,OptionsPattern[]]:=Block[
{tmp,tmpr=0,null,i,xx,yy,a,b,bb,deriv=OptionValue[Derivate],disp=OptionValue[Dispersion],sub=OptionValue[Subtraction],im=OptionValue[Im],p=factor[[1]],t=factor[[2]],s},

If[(sub>0) && (deriv>0),Print["Option conflict!"];Abort[]];
tmp=expr//FCI;

(*
If[!FreeQ[tmp,FeynAmpDenominator],
	tmp=FeynAmpDenominatorSplit[tmp]/.FeynAmpDenominator[PropagatorDenominator[Momentum[p_,dim___],mass_]]:>
	1/(Pair[Momentum[p,dim],Momentum[p,dim]]-mass^2)
];(* FAD[p,m] \[Rule] 1/(SPD[p] - m^2) *)
*)(* allow Borel transform before evaluate the diagram *)

If[!FreeQ[tmp,Pair[LorentzIndex[__],Momentum[__]]]||!FreeQ[Eps[___,Momentum[__]]],
	Print["Lorentz vector involed, the result may not desired. consider use QGather first"]
];

(*------------------------------------------------------------------------*)

If[disp,
(* act Borel transformation on dispersion integral *)
(* \[PartialD]^n f(t) = n!/(2\[Pi]I) \[Integral] ds f(s)/(s-t)^(n+1)*)

	s=If[Length[factor]!=3,Print["check the input!"];Abort[],factor[[3]]];
	tmp=tmp/.{Pair[Momentum[p,___],Momentum[p,___]]->s,Log[pp_]:>Log[pp/.{4Pi ScaleMu^2->1,ScaleMu^2->1}]};


	tmp=If[im,
			tmp=ExpandAll[tmp/.{Log[-s]:>Log[s]-I Pi, Power[s,nn_Integer]/;Negative[nn]:>-I Pi/(nn!) (-t)^(nn-1)}];
			tmp=tmp-(tmp/.Complex[_,_]->0);
			tmp=tmp/.{tt__ Complex[rr_,ii_]:> tt ii,Complex[rr_,ii_]:>ii}
		,
			tmp
		];

	tmpr=1/Pi t^(deriv) Exp[-s t]tmp

,
(*----------------------------------------------------------------------*)
(* act Borel transformation directly *)
	If[im,
(*tmp=ExpandAll[tmp/.{Log[-1x__]:>Log[Times[x]]-I Pi,Log[Rational[-1,y_]x__]:>Log[1/y Times[x]]-I Pi}];*)

		tmp=tmp-(tmp/.Complex[_,_]->0);
		tmp=tmp/.{tt__ Complex[rr_,ii_]:> tt ii,Complex[rr_,ii_]:>ii}
	];(* subtract pure real term; get the imaginary part *)

	If[deriv>0,tmp=D[tmp/.Pair[Momentum[p,___],Momentum[p,___]]:>Pair[Momentum[p,D],Momentum[p,D]],
		{Pair[Momentum[p,D],Momentum[p,D]],deriv}]
	];(* derivate *)

	If[sub>0,tmp=tmp/(Pair[Momentum[p,D],Momentum[p,D]]^sub)];(* subtractions in dispersion integral *)

(* get the power of p^2 and Log[-p^2] *)
	tmp=tmp/.{Pair[Momentum[p,___],Momentum[p,___]]:> a , Log[y_ Pair[Momentum[p,___],Momentum[p,___]]]:>b Log[bb y]};


	tmp=(ExpandAll[tmp]+null);
(*------------------------------------------------*)
	For[i=1,i<Length[tmp]+1,i++,
		xx=Exponent[tmp[[i]],a];
		yy=Exponent[tmp[[i]],b];

		If[yy<0,Print["negative power of Log involved.
			the terms have negative power of Log will be discard"]];

		If[yy>2,Print["high order power of Log will be discard"]];

(* Borel transformation *)
		If[xx<0&&yy==0,tmpr=tmpr+tmp[[i]](-1)^(-xx) t^(-xx)/Gamma[-xx]];


		If[xx>=0&&yy==1,tmpr=tmpr-tmp[[i]]/.Log[bb y_]:>Gamma[xx+1] t^(-xx)];

		If[xx>=0&&yy==2,tmpr=tmpr+tmp[[i]]/.Log[bb y_]:>2Gamma[xx+1]t^(-xx) (1/t -Sum[1/j,{j,1,xx}])];


		If[xx<0&&yy==1,tmpr=tmpr+tmp[[i]]/.Log[bb y_]:>((-1)^(-xx)t^(-xx) (-Log[-t/y]+PolyGamma[-xx])/Gamma[-xx])];

		If[xx<0&&yy==2,tmpr=tmpr+tmp[[i]]/.Log[bb y_]^2:>((-1)^(-xx)t^(-xx)  (Log[-t/y]^2-2PolyGamma[-xx]Log[-t/y]+PolyGamma[-xx]^2 -PolyGamma[1,-xx])/Gamma[-xx])];

];

	tmpr=1/t tmpr/.{a->1,b->1}
];


tmpr//Simplify

]











End[]