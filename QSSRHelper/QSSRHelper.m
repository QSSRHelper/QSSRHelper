(* Wolfram Language Package *)


(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2021 Shuang-Hong Li
*)


(* Created by the Wolfram Workbench 2021/12/14 *)

BeginPackage["QSSRHelper`",{"FeynCalc`"}]

Print[Style["QSSRHelper","Text",Bold],Style["  is a package used for QCD Sum Rules calculation","Text"]];



(*-------------------------------------------------------------------------------------------*)
(* Define some symbols *)

Condensate::usage = 
	"Condensate[condensate] generate the symbol of coorsponding condensate"



qfact1::usage =
	"qfact1[] is just a symbol for combine constant factors involved in Feynman integral and Fourier transformation"
	
	
qfact2::usage =
	"qfact2[] is just a symbol for combine constant factors of Gamma function symbols in qfact1"
	

GStrength::usage = 
	"GStrength[mu,nu,a,b___] is the gluontensor tensor symbol \!\(\*SubscriptBox[SuperscriptBox[\(G\), \(a\)], \(\[Mu]\[Nu]\)]\)"
	
	
qGamma2::usage = 
"qGamma2[expr] is a special qGamma function, which show \[Epsilon]-pole explicitly";


qGamma::usage = 
"qGamma[x] is just qGamma symble and doesn't do any evaluation";



qTFI::usuage = "qTFI[{u_,v_,r_,s_,t_},{v1_,v2_,v3_,v4_,v5_},{k1_,k2_,p_,{Rules___}}] not do any evalutaiton;
 it keep the {k1_,k2_,p_,{Rules___}} to indicate where the 2-loop comes form."

	

(*-------------------------------------------------------------------------------------------*)

Options[qGamma2]={
	D->4-2Epsilon,
	Expand->False};


Options[AgammaD] = {
	Dimension->D}

(*-------------------------------------------------------------------------------------------*)
Begin["`Private`"]
(* Implementation of the package *)


(*-------------------------------------------------------------------------------------------*)


qfact1 /: MakeBoxes[qfact1[expr_],TraditionalForm]:=
	RowBox[{"(",ToBoxes[expr,TraditionalForm],")"}];
	
qfact1[xx_Integer]:=xx
qfact1[xx_Rational]:=xx

(*-------------------------------------------------------------------------------------------*)

qfact2/: MakeBoxes[qfact2[expr_],TraditionalForm]:=
	RowBox[{"(",ToBoxes[expr,TraditionalForm],")"}];
	
qfact2[xx_Integer]:=xx
qfact1[xx_Rational]:=xx

(*-------------------------------------------------------------------------------------------*)

Condensate[xx__]:=Times@@(Condensate[#]&/@List[xx])



Condensate[x_]:=Block[{expr,tmp,list},
expr=ToString[x];

list={{"qq",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"d3",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"ss",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["s", "_"],"s","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"mqq",RowBox[{"m","\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"msqq",RowBox[{SubscriptBox["m","s"],"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"mss",RowBox[{SubscriptBox["m","s"],"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["s", "_"],"s","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"qgq",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"G","q","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"sgs",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["s", "_"],"G","s","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"d6",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q",SuperscriptBox["\[RightAngleBracket]", "2"]}]},
	{"qq2",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q",SuperscriptBox["\[RightAngleBracket]", "2"]}]},
	{"ss2",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["s", "_"],"s",SuperscriptBox["\[RightAngleBracket]", "2"]}]},
	{"gg",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]","G","G","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"d4",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]","G","G","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"g2",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]","G","G","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"g3",RowBox[{"\[LeftAngleBracket]","",SuperscriptBox["G", "3"]"","\[RightAngleBracket]"}]},
	{"ggg",RowBox[{"\[LeftAngleBracket]","",SuperscriptBox["G", "3"]"","\[RightAngleBracket]"}]},
	{"q2qgq",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q","","\[RightAngleBracket]","\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"G","q","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"qqqgq",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q","","\[RightAngleBracket]","\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"G","q","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"d8",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q","","\[RightAngleBracket]","\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"G","q","\[ThinSpace]","\[RightAngleBracket]"}]},
	{"qq3",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q",SuperscriptBox["\[RightAngleBracket]", "3"]}]}};
	
	
	If[!FreeQ[list,expr],
		tmp=Position[list,expr][[1,1]];
		DisplayForm[TraditionalForm[list[[tmp,2]]]]
		,
		DisplayForm[TraditionalForm[RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",expr,"","\[RightAngleBracket]"}]]]
	]

]


(*-------------------------------------------------------------------------------------------*)

GStrength/:MakeBoxes[GStrength[mu_,nu_,a_,b___],TraditionalForm]:=Block[{l={b}},
If[Length[l]==0,
	RowBox[{SubsuperscriptBox["G",StringJoin[ToString[mu],ToString[nu]],ToString[a]]}],
	
	If[Length[l]==1,
	RowBox[{SubscriptBox["D",ToString[b]],SubsuperscriptBox["G",StringJoin[ToString[mu],ToString[nu]],ToString[a]]}],
		If[Length[l]==2,
			RowBox[{SubscriptBox["D",ToString[l[[1]]]],SubscriptBox["D",ToString[l[[2]]]],SubsuperscriptBox["G",StringJoin[ToString[mu],ToString[nu]],ToString[a]]}]
		]
	]
]

]

(*-------------------------------------------------------------------------------------------*)

qGamma /: MakeBoxes[qGamma[x_],TraditionalForm]:=
	RowBox[{"\[CapitalGamma]","(",ToBoxes[ExpandAll[x],TraditionalForm],")"}];
(*qGamma[1]=1;
qGamma[2]=1;
qGamma[3]=2;
*)
(* keep all \[CapitalGamma] unevaluated to avoid some error/bug be hidden in function like FourierXP, Qdx : e.g. \[CapitalGamma][2]\[CapitalGamma][0]-\[CapitalGamma][1]\[CapitalGamma][0] = 0  
  although the equality hold, but the \[CapitalGamma][0] indicate there have something wrong in evaluation/input *)

(*-------------------------------------------------------------------------------------------*)

qGamma2[y_,OptionsPattern[]]:=Block[
{t,n,tmp,dim=OptionValue[D],eps=0,order=OptionValue[Expand],result},

(*If[FreeQ[y,D]&&FreeQ[y,Epsilon]&&FreeQ[y,_Integer],Print["check input!"];Abort[]];*)

t = y/.D->dim//Expand;

n = t/. Epsilon->0;
eps = t - n ;

If[n<=0 ,
	tmp=(-1)^n /eps Gamma[1-eps]Gamma[1+ eps]/Gamma[-n+1 -eps];
	
	If[IntegerQ[order]&&order>=0, 
		tmp=Series[tmp,{Epsilon,0,order}]//Normal
		(*result=Sum[tmp[[3]][[i]] tmp[[1]]^(tmp[[4]]+i-1),{i,1,tmp[[5]]-tmp[[4]]}],
		result = tmp*)
	];
	result=tmp
,
		
	result=Gamma[t]
];

result	
]





(*-------------------------------------------------------------------------------------------*)
(* show the TFI with momentum k1, k2, p and perhaps the rules of shift and/or rescale the k1, k2, to indicate how this 2-loop integral getted *)
qTFI[list1_,list2_,{k1_,k2_,p_,rules_List}]/;!FreeQ[rules,List,{2}]:=
	If[Plus@@list1==0,
		qTFI[Tarcer`TFI[D,(p/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb})^2,list2],
				{k1,k2,p/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb},DeleteCases[Flatten[rules],Rule[a_,a_]]}]
																	
	,
		qTFI[Tarcer`TFI[D,(p/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb})^2,list1,list2],
				{k1,k2,p/.{-aa_:>aa,aa_+bb_/;!FreeQ[aa,-1]&&!FreeQ[bb,-1]:>-aa-bb},DeleteCases[Flatten[rules],Rule[a_,a_]]}]
	]

																																				
(*-------------------*)

qTFI[aa_,{k1_,k2_,p_,{}}]:=qTFI[aa,{k1,k2,p}]




(*-------------------------------------------------------------------------------------------*)





(*-------------------------------------------------------------------------------------------*)

End[]







(*-------------------------------------------------------------------------------------------*)


(* Quote all symbols before load their definitions, make the symbols in different files know each other *)

files=Flatten[{FileNames[ "*.m",FileNameJoin@{DirectoryName[$InputFileName],"Evaluation"}],
			FileNames[ "*.m",FileNameJoin@{DirectoryName[$InputFileName],"Fourier"}],
			FileNames[ "*.m",FileNameJoin@{DirectoryName[$InputFileName],"Loop"}],
			FileNames[ "*.m",FileNameJoin@{DirectoryName[$InputFileName],"Style"}],
			FileNames[ "*.m",FileNameJoin@{DirectoryName[$InputFileName],"Lorentz"}],
			FileNames[ "*.m",FileNameJoin@{DirectoryName[$InputFileName],"Auxiliary"}]}];
			

symbols=StringSplit[StringSplit[#,"\\"|"/"][[-1]],"."][[1]]&/@files;
symbols=StringJoin["QSSRHelper`",#]&/@symbols;

ToExpression[#]&/@symbols;


(* Load the functions *)
Get/@files



(*-------------------------------------------------------------------------------------------*)

EndPackage[]

