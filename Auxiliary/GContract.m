(* Wolfram Language package *)

(* Author: ShungHong Li *)



GContract::usage = 
	"GContract[expr] is a function which turn \!\(\*SubscriptBox[SuperscriptBox[\(G\), \(a\)], 
\(\(\[Mu]\[Nu]\)\(\\\ \)\)]\)\!\(\*SubscriptBox[SuperscriptBox[\(G\), \(b\)], \(\[Rho]\[Sigma]\)]\) to \!\(\*SuperscriptBox[\(\[Delta]\),
 \(ab\)]\)/(8D(D-1)) (\!\(\*SubscriptBox[\(g\), \(\[Mu]\[Nu]\[Rho]\)]\)\!\(\*SubscriptBox[\(g\), \(\[Nu]\[Sigma]\)]\) - \!\(\*SubscriptBox[\(g\), \(\[Mu]\[Sigma]\)]\)\!\(\*SubscriptBox[\(g\), \(\[Nu]\[Rho]\)]\))<GG> "
 
 
 
 Begin["`Private`GContract`"]
 
 
GContract[expr_]:=Block[{tmp},
tmp=expr//FCI;
(*tmp//.Dot[a___,Times[GStrength[x___],b___],c___]\[RuleDelayed]Dot[a,Times[b],c]GStrength[x];*)

tmp=Collect[Expand[tmp],GStrength[_]];
tmp/.GStrength[l1_,l2_,a_]GStrength[l3_,l4_,b_]:>1/(8D(D-1)) SUNDelta[SUNIndex[a],SUNIndex[b]]Condensate["gg"](MTD[l1,l3]MTD[l2,l4]-MTD[l1,l4]MTD[l2,l3])
]

 
 
 
 
 
 
 End[]