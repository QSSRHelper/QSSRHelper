(* ::Package:: *)

(* Wolfram Language package *)

(* Author: ShungHong Li *)



IntegrateLog::usage =
"IntegrateLog[expr,{x,lb,ub}] is special Integrate deal with Log function based on integral by parts"






Begin["`Private`IntegrateLog`"]




Options[IntegrateLog] = {
	Limit->Auto};







(*---------------------------------------------------------------*)

IntegrateLog[expr_,{s_,sl_,su_},opt:OptionsPattern[]]:=Block[{opt2,opt3,limit,tmp,liml=0,limu=0},
opt2={opt};

limit=If[FilterRules[{opt2},Limit]=={},"Auto",FilterRules[{opt2},Limit][[1,2]]];
opt3=FilterRules[{opt2},Except[{Limit,GeneratedParameters,PrincipalValue,Direction}]];
opt2=FilterRules[{opt2},Except[{Limit,Direction,Method,PerformanceGoal}]];


If[ToString[sl]==ToString[su],
	0
,
	tmp=If[opt2==={},IntegrateLog[expr,s],IntegrateLog[expr,s,opt2]];

	If[(Length[limit]==2)&&NumberQ[limit[[1]]]&&NumberQ[limit[[2]]],
		If[opt3==={},
			(Limit[tmp,s->su,Direction->limit[[2]]]) -(Limit[tmp,s->sl,Direction->limit[[1]]])
		,
			(Limit[tmp,s->su,Direction->limit[[2]],opt3]) -(Limit[tmp,s->sl,Direction->limit[[1]],opt3])
		]
	,


		If[ToLowerCase[ToString[limit]]=="auto",
(* sl for lower bound, su for up bound. the direction of limit is seted to approach the integral bound, if at least one of sl and su is a specified number of infinity.
  and the direction of integral is supposed:
  for sl and su are speficied number, along the direction sl -> su
  for one speficied real number, along the direction - -> +
 for one speficied comeplex number, along the direction 0 -> sl or 0 -> su, if sl or su is speficied
   for one infinity, along the direction sl -> 0 or 0 -> su, if |sl| or |su|=infinity
for |sl|=|su|=infinity and they differ by a sign, along the direction sl -> 0 -> su 
 *)
			If[NumberQ[sl]&&NumberQ[su],
				{liml,limu}={sl-su,su-sl}
			,
				If[(NumberQ[sl]||NumberQ[su])&&FreeQ[{su,sl},DirectedInfinity],
					{liml,limu}={sl,su}/.{{a_?NumberQ,___}/;Im[a]==0:>{-1,1},{___,a_?NumberQ}/;Im[a]==0:>{-1,1},
					{a_?NumberQ,___}/;Im[a]!=0:>{-a,a},{___,a_?NumberQ}/;Im[a]!=0:>{-a,a}}
				,
					If[Xor[FreeQ[su,DirectedInfinity],FreeQ[sl,DirectedInfinity]],
						{liml,limu}={sl,su}/.{{DirectedInfinity[a_],___}:>{a,-a},{___,DirectedInfinity[a_]}:>{-a,a}}
					,
						If[Nor[FreeQ[su,DirectedInfinity],FreeQ[sl,DirectedInfinity]],
							{liml,limu}={sl,su}/.{DirectedInfinity[a_],DirectedInfinity[b_]}/;(a+b==0):>{a,-a}
						]
					]
				]
			];



			If[{liml,limu}=={0,0},
				If[opt3==={},
					(Limit[tmp,s->su]) -(Limit[tmp,s->sl])
				,
					(Limit[tmp,s->su,opt3]) -(Limit[tmp,s->sl,opt3])
				]
			,
				If[opt3==={},
					(Limit[tmp,s->su,Direction->limu]) -(Limit[tmp,s->sl,Direction->liml])
				,
					(Limit[tmp,s->su,Direction->limu,opt3]) -(Limit[tmp,s->sl,Direction->liml,opt3])
				]
			]
			
		,
			(tmp/.s->su) - (tmp/.s->sl)
		]
	]
]


]

(*---------------------------------------------------------------*)

IntegrateLog[expr_,x:Except[_?ListQ],opt:OptionsPattern[]]:=Block[
{tmp,tmp2,res,null,null0,null2,i,int,int2,log,log2,opt2,depth,j},
opt2=FilterRules[{opt},Except[{Limit,Direction,Method,PerformanceGoal}]];


tmp=Replace[Expand[null(null0+expr)],{Log[z_]:>log2[z],Log[z_]^n_Integer/;n>0:>log2[z]^n},{2}];
(* null and null0 are set to unify the expression, so that only the polynomial of Log will be involved *)

tmp2=tmp/.log2[_]->0;(* seprate the terms Log not involved *)

tmp=int[tmp-tmp2]/.log2[t_]^n_:>Product[log2[null2[i] t],{i,0,n-1}];(* Log^n -> Log * log * ... ; insert null2[i] to avoid Mathematica simplify them to Log^n*)
(*(i+=1; log2[t]^(n-1) log2[null2[i] t])*)

tmp=tmp//.int[c_]/;!FreeQ[c,log2] :>(c/.a_ log2[t_] :>int[null a]log[t]-int2[int[null a] D[t,x]/t]); (* intergal by part nutill no log2 *)


tmp=(tmp/.{null->1,null0->0,null2[_]->1,log->Log,log2->Log});
depth=Depth[tmp];






If[opt2==={},

	For[j=1,j<depth,j++;
		tmp=Replace[tmp,{int[z_]:>Integrate[z,x],int2[z_]:>Integrate[z,x]},{depth-j},Heads->True];
	];


	res=tmp+Integrate[tmp2/.{null->1,null0->0},x]


,


	For[j=1,j<depth,j++;
		tmp=Replace[tmp,{int[z_]:>Integrate[z,x,opt2],int2[z_]:>Integrate[z,x,opt2]},{depth-j},Heads->True];
	];

(*//.{int[z_]:>Inactive[Integrate[z,x,#]&@opt2],int2[z_]:>Inactive[Integrate[z,x,#]&@opt2]};*)(* evaluate the integrate *)

	res=tmp+Integrate[tmp2/.{null->1,null0->0},x,opt2]

]




]





(*---------------------------------------------------------------*)





End[]
