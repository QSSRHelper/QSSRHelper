(* Wolfram Language package *)

(* Author: ShungHong Li *)





IndexSimplify::usage =
	"IndexSimplify[expr] simplify the dummy Lorentz index in \[Gamma]-matrices"	
	
	
Begin["`Private`IndexSimplify`"]



Options[IndexSimplify] = {
	Cyclic->False}




IndexSimplify[expr_,OptionsPattern[]]:=Block[
{tmp,tmp2,tmp3,cycl,dup,result=0,null,null0,plus,dot,i,j,k},

tmp=null (expr+null0 GAD[a,b])//Expand//FCI;
tmp=Replace[tmp,Plus->plus,{1},Heads->True];
tmp=tmp/.Dot->dot;
tmp2=tmp/.a___ dot[b___]:>dot[b];


tmp2=tmp2/.{DiracGamma[LorentzIndex[a_,___],___]:>a,DiracGamma[5]->-1};

If[OptionValue[Cyclic]===True,

	tmp2=tmp2/.dot[a___]:>(cycl={{a}};
	
							For[k=1,k<Length[{a}],k++,
								cycl=Append[cycl,RotateLeft[cycl[[-1]] ]] 
							];
							dummy[#]&/@cycl
						);
	
	
	For[i=1,i<Length[tmp2]+1,i++,
	
		If[tmp2[[i]]=!=0,
			tmp3=!FreeQ[#,tmp2[[i,1]]]&/@tmp2;
			dup=Position[tmp3,True];
			tmp2=ReplacePart[tmp2,Thread[Rule[dup,0]]];
			
			result=result+(tmp[[ dup[[1]] ]]/.a___ dot[b___]:>dot[b])(Sum[tmp[[j]],{j,dup}]/.dot[___]->1);
		];
		
	];		
,

	tmp2=tmp2/.dot[a___]:>dummy[{a}];

	For[i=1,i<Length[tmp2]+1,i++,

		If[tmp2[[i]]=!=0,
			dup=Position[tmp2,tmp2[[i]] ];
			tmp2=ReplacePart[tmp2,Thread[Rule[dup,0]]];

			result=result+(tmp[[ dup[[1]] ]]/.a___ dot[b___]:>dot[b])(Sum[tmp[[j]],{j,dup}]/.dot[___]->1);
		]

	];

];


result/.{dot->Dot,plus->Plus,null->1,null0->0}
]



(* generate a list of indices used as dummy indices in IndexSimplify[] *)
dummy[expr_List]:=Block[{tmp0,tmp,tmp2={},index,i,j,p,l},
	
l=Length[expr];
tmp=Table[0,l];

If[!FreeQ[expr,-1],tmp[[ Position[expr,-1][[1]] ]]=-1];

For[i=1,i<l,i++,
	If[!FreeQ[expr[[i+1;;]],expr[[i]]],
		
		p=Position[expr,expr[[i]]][[2]];
		tmp[[i]]=i;
		tmp[[p]]=i;
		tmp2=Append[tmp2,expr[[i]]]
	]
];

If[tmp===Table[0,l],expr,tmp]

]






End[]	