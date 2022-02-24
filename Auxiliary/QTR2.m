(* Wolfram Language package *)

(* Author: ShungHong Li *)






QTR2::usage = 
	"QTR[expr] is a special TR with Larin Scheme, which force to move \!\(\*SuperscriptBox[\(\[Gamma]\), \(5\)]\) anticommuting to right in TR;
		while in TR function the \!\(\*SuperscriptBox[\(\[Gamma]\), \(5\)]\) is move to right by cyclicity"	
		
		

Begin["`Private`QTR2`"]



QTR2[expr_]:=Block[{tmp,tmp2,i,null0,dot,resu=0,scheme},
tmp=expr//FCI;

If[FreeQ[tmp,DiracGamma],

	resu=tmp,

	scheme=FCGetDiracGammaScheme[];
	FCSetDiracGammaScheme["Larin"];

(* the replacement  Dot[a___,Times[b___,Dot[c_]],d___]\[RuleDelayed]Times[b] Dot[a,c,d] works messy; replace Dot as an undefined symbol to protect *)
	tmp=tmp/.Dot->dot;
	tmp=tmp//.a_ b_:>Distribute[a b];

	tmp=tmp//.dot[a___,Plus[b_,bb__],c___]:> dot[a,b,c]+ dot[a,bb,c];
	tmp=tmp//.{
	dot[a___,Times[b___,dot[c___]],d___]:> b dot[a,c,d],
	dot[a___,Times[b___,c_DiracGamma|c_SUNT],d___]:>b dot[a,c,d] };

	tmp=tmp+null0/.dot->Dot;

	For[i=1,i<Length[tmp]+1,i++,
		tmp2=tmp[[i]];
		tmp2=tmp2//.a___ . DiracGamma[5] . b_ . c___ :> If[FreeQ[b,DiracGamma], a . b . DiracGamma[5] . c ,
													If[ToString[b]=="DiracGamma[5]",a . c,  -1 a . b . DiracGamma[5] . c ]];
		tmp2=tmp2/.Dot[z_]:>TR[Dot[z]];
		resu=resu+tmp2

	];
];

FCSetDiracGammaScheme[scheme];
resu/.null0->0
]




End[]