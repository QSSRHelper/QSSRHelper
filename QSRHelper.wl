(* ::Package:: *)

-
(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2020 ShuangHong Li
*)

(*
	QSRHelper is a package used for some calculation in QCD Sum Rules.
	Notice: This software is not completed. For basic usage, see usage.nb and example.nb 
*)

BeginPackage["QSRHelper`",{"FeynCalc`"}]

Print[Style["QSRHelper","Text",Bold],Style["  is a package contain some useful function","Text"]];

FourierXP::usage = 
"FourierXP[expr,{x,p}] is D-dimensional Fourier Transformation from
coordinate space {x} to momentum space {p}";
 
FourierPX::usage =
"FourierPX[expr,{p,x}] id D-dimensional Fourier Transformation from
momentum space {p} to coordinate space {x}. 
It's equivalant to set Option Inverse->True in FourierXP";

GFourierXP::usage =
"GFourierXP[n,{p,indexlist}] generate Fourier Transformation and it's derivative";

GFourierPX::usage =
"GFourierPX[n,{x,indexlist}] generate inverse Fourier Transformation and it's derivative";

Qamma::usage = 
"Qamma[expr] is a special Qamm function, which show \[Epsilon]-pole explicitly";

Qamm::usage = 
"Qamm[x] is just Qamm symble and doesn't do any evaluation";

QDimension::usage = 
"QDimension[expr,dim] set dimension D -> dim in power and Qamm";

IntegrateLog::usage =
"IntegrateLog[expr,{x,lb,ub}] is special Integrate deal with Log function based on integral by parts"

QEvaluate::usage = 
"QEvaluate[expr,Order->0] evaluating the Fourier transformation, expand to O(\[Epsilon]^Order) "

QGather::usage =
"QGather[expr,p,Table\[Rule]True,
	SeparateTransverse\[Rule]True] is a function gather the expr to a more symmetry form about Lorentz structure"


Borel::usage = 
	"Borel[expr,{momentum,parameter}] is Borel transformation"

Qdx::usage = 
	"Qdx[expr,x] is a simple feyman integral in coordinate space for two feynman parameters"
	
Qdp::usage =
	"Qdq[expr,p] is a simple feyman integral in momentum space for two feynman parameters"
	
	
QTR::usage = 
	"QTR[expr] is a special TR with Larin Scheme, which force to move \!\(\*SuperscriptBox[\(\[Gamma]\), \(5\)]\) anticommuting to right in TR;
		while in TR function the \!\(\*SuperscriptBox[\(\[Gamma]\), \(5\)]\) is move to right by cyclicity"
		
Condensate::usage = 
	"Condensate[condensate] generate the symbol of coorsponding condensate"
	
GStrength::usage = 
	"GStrength[mu,nu,a,b___] is the gluontensor tensor symbol \!\(\*SubscriptBox[SuperscriptBox[\(G\), \(a\)], \(\[Mu]\[Nu]\)]\)"
	
GContract::usage = 
	"GContract[expr] is a function which turn \!\(\*SubscriptBox[SuperscriptBox[\(G\), \(a\)], 
\(\(\[Mu]\[Nu]\)\(\\\ \)\)]\)\!\(\*SubscriptBox[SuperscriptBox[\(G\), \(b\)], \(\[Rho]\[Sigma]\)]\) to \!\(\*SuperscriptBox[\(\[Delta]\),
 \(ab\)]\)/(8D(D-1)) (\!\(\*SubscriptBox[\(g\), \(\[Mu]\[Nu]\[Rho]\)]\)\!\(\*SubscriptBox[\(g\), \(\[Nu]\[Sigma]\)]\) - \!\(\*SubscriptBox[\(g\), \(\[Mu]\[Sigma]\)]\)\!\(\*SubscriptBox[\(g\), \(\[Nu]\[Rho]\)]\))<GG> "
 
 QExpand::usage = 
	"QExpand[expr] use ExpandAll then expand all dot product with dirac structure."
	
	
QAverage::usage = 
	"QAverage[expr,p] is a function which average momentum vectors to scalar product with metrices tensor"
	
	
	
AgammaD::usage =
	"AgammaD[expr] generate normalized D-dimensional gamma matrices with antisymmetry indices"
	
Agamma::usage =
	"Agamma[expr] generate normalized gamma matrices with antisymmetry indices"
	
	
IndexSimplify::usage =
	"IndexSimplify[expr] simplify the dummy Lorentz index in \[Gamma]-matrices"	


Begin["`Parivate`"]

Options[FourierXP]={
	TrueGamma->Integer,
	Dimension->"AsIs",
	Inverse->False};
	
	
Options[FourierPX]={
	TrueGamma->Integer,
	Dimension->"AsIs"};
	
Options[QDimension]={
	D->4-2Epsilon};	
	
Options[Qamma]={
	D->4-2Epsilon,
	Expand->False};


Options[GFourierXP] = {
	TrueGamma->Integer,
	Dimension->D};
	
Options[GFourierPX] = {
	TrueGamma->Integer,
	Dimension->D};
	
Options[IntegrateLog] = {
	Limit->Auto};
	
Options[QEvaluate] = {
	D->4-2Epsilon,
	Order->0,
	Scheme->null}
	
Options[QGather] = {
	Table->True,
	SeparateTransverse->True,
	Subtract->None}	
	
Options[Borel] ={
	Derivate->0,
	Subtraction->0,
	Dispersion->False,
	Im->False}
	
	
Options[Qdx] = {
	Contract->False,
	dp->False,
	lessdummy->True,
	Simplify->False}	
	
Options[Qdp] = {
	Contract->False,
	lessdummy->True,
	Simplify->False}
	
Options[AgammaD] = {
	Dimension->D}
	
Options[IndexSimplify] = {
	Cyclic->False}


Options[qExpand] = {
	lessdummy->False}


GContract[expr_]:=Block[{tmp},
tmp=expr//FCI;
(*tmp//.Dot[a___,Times[GStrength[x___],b___],c___]\[RuleDelayed]Dot[a,Times[b],c]GStrength[x];*)

tmp=Collect[Expand[tmp],GStrength[_]];
tmp/.GStrength[l1_,l2_,a_]GStrength[l3_,l4_,b_]:>1/(8D(D-1)) SUNDelta[SUNIndex[a],SUNIndex[b]]Condensate["gg"](MTD[l1,l3]MTD[l2,l4]-MTD[l1,l4]MTD[l2,l3])
]


Condensate[x_]:=Block[{expr,tmp,list},
expr=ToString[x];

list={{"qq",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q","\[ThinSpace]","\[RightAngleBracket]"}]},
{"ss",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["s", "_"],"s","\[ThinSpace]","\[RightAngleBracket]"}]},
{"mqq",RowBox[{"m","\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q","\[ThinSpace]","\[RightAngleBracket]"}]},
{"msqq",RowBox[{"m","\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["s", "_"],"s","\[ThinSpace]","\[RightAngleBracket]"}]},
{"mss",RowBox[{"m","\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["s", "_"],"s","\[ThinSpace]","\[RightAngleBracket]"}]},
{"qgq",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"G","q","\[ThinSpace]","\[RightAngleBracket]"}]},
{"sgs",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["s", "_"],"G","s","\[ThinSpace]","\[RightAngleBracket]"}]},
{"qq2",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q",SuperscriptBox["\[RightAngleBracket]", "2"]}]},
{"ss2",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["s", "_"],"s",SuperscriptBox["\[RightAngleBracket]", "2"]}]},
{"gg",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]","G","G","\[ThinSpace]","\[RightAngleBracket]"}]},
{"g2",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]","G","G","\[ThinSpace]","\[RightAngleBracket]"}]},
{"g3",RowBox[{"\[LeftAngleBracket]","",SuperscriptBox["G", "3"]"","\[RightAngleBracket]"}]},
{"ggg",RowBox[{"\[LeftAngleBracket]","",SuperscriptBox["G", "3"]"","\[RightAngleBracket]"}]},
{"qq3",RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",OverscriptBox["q", "_"],"q",SuperscriptBox["\[RightAngleBracket]", "3"]}]}};


If[!FreeQ[list,expr],
	tmp=Position[list,expr][[1,1]];
	DisplayForm[TraditionalForm[list[[tmp,2]]]]
	,
	DisplayForm[TraditionalForm[RowBox[{"\[LeftAngleBracket]","\[ThinSpace]",expr,"","\[RightAngleBracket]"}]]]
]

]


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


Qamm /: MakeBoxes[Qamm[x_],TraditionalForm]:=
	RowBox[{"\[CapitalGamma]","(",ToBoxes[ExpandAll[x],TraditionalForm],")"}];

(* keep all \[CapitalGamma] unevaluated to avoid some error/bug be hidden in function like FourierXP, Qdx : e.g. \[CapitalGamma][2]\[CapitalGamma][0]-\[CapitalGamma][1]\[CapitalGamma][0] = 0  
  although the equality hold, but the \[CapitalGamma][0] indicate there have something wrong in evaluation/input *)




QDimension[expr_,OptionsPattern[]]:=Block[{temp,dim=OptionValue[D]},
temp=FCReplaceD[expr,D->dim];
temp=(temp/.{Qamm[x_]:>Qamm[Expand[x/.D->dim]],Gamma[x_]:>Gamma[Expand[x/.D->dim]]})/.Power[a_,b_]:>Power[a,Expand[b/.D->dim]]
];







Qamma[y_,OptionsPattern[]]:=Block[
{t,n,tmp,dim=OptionValue[D],eps=0,order=OptionValue[Expand],result},

If[FreeQ[y,D]&&FreeQ[y,Epsilon]&&FreeQ[y,_Integer],Print["check input!"];Abort[]];

t = y/.D->dim//Expand;

n = t/. Epsilon->0;
eps = t - n ;

If[n<=0 ,
	tmp=(-1)^n /eps Gamma[1-eps]Gamma[1+ eps]/Gamma[-n+1 -eps];
	If[IntegerQ[order]&&order>=0, 
		tmp=Series[tmp,{Epsilon,0,order}];
		result=Sum[tmp[[3]][[i]] tmp[[1]]^(tmp[[4]]+i-1),{i,1,tmp[[5]]-tmp[[4]]}],
		result = tmp],
		
	result=Gamma[t]
];

result	
];




GFourierXP[m_,v_,OptionsPattern[]]:=Block[
{i,j,n,temp,co,result,p,l,opt=OptionValue[TrueGamma],dim=OptionValue[Dimension],dims,null},

l=Length[v];
If[l>1,p=v[[1]],p=v];
(* v = {p, \[Mu],\[Nu],...}. the \[Mu],\[Nu]... represent partial differentiate: -i\[PartialD]/\[PartialD]p^\[Mu] -i\[PartialD]/\[PartialD]p^\[Nu]...*)
If[dim==4,dims=4,dims=D];

n=m/.\[Epsilon]->Epsilon;(* allow writte Epsilon as \[Epsilon] for convenient *)

co=-I (-1)^n 2^(dim-2n) Pi^(dim/2) Qamm[dim/2 - n]/Qamm[n];(*coefficient*)

temp=(-Pair[Momentum[p,dims],Momentum[p,dims]])^null[-dim/2+n];

If[l>0,

	For[j=1, j<l, j++,
	temp = -I FourDivergence[temp, Pair[LorentzIndex[v[[-j]],dims],Momentum[p,dims]]];
	temp =temp/.{Times[null[xx_]+yy_,zz_]-> -zz Qamm[-xx-yy+1]/Qamm[-xx-yy],Times[null[xx_],zz_]-> -zz Qamm[-xx +1]/Qamm[-xx]}]
];(*derivative if need;incorporate Qamm[] with the factor generated by derivative *)

result=co temp/.null[x_]->x//Simplify;


If[opt==Integer, result=result/.Qamm[nn_Integer]:>Gamma[nn]];

If[opt==All,result=result/.Qamm:>Qamma];

result
]
(*----------------------------------------------------------------*)
(* the Inverse is samliar, except the overall factor -1/(2\[Pi])^D, 
and replace every -i\[PartialD] \[Rule] i\[PartialD] which can be absorbed in overall sign*)

GFourierPX[m_,v_,OptionsPattern[]]:=Block[{opt=OptionValue[TrueGamma],l,dim=OptionValue[Dimension]},

l=If[Length[v]==0,1,Length[v]];

(-1)^l/(2Pi)^(4-2Epsilon)GFourierXP[m,v,TrueGamma->opt,Dimension->dim]]







(* The basic logic is expand expr to several terms so that it have form:
                     ...(x^\[Nu])(x^\[Mu])((1/x^2)^n)+ ...(1/X^2)^m+...
then do fourier transformation term by term *)



FourierXP[expr_,{x_,pp_},OptionsPattern[]]:=Block[
{tmp,ttmp,test,rule1,dindex,findex,f,fco,result=0,tempresult,opt=OptionValue[TrueGamma],
inverse=OptionValue[Inverse],sign=-1,factor=1,null1,null2,null3,null4,null5,nulllo,nullpo,nullindx,Flist={},lorindx={},mompo,times,li,wrong,di,i,j,k,mdim,p
},

tmp=Collect[Contract[expr]//FCI,Qamm[___]]//Expand;

If[FreeQ[tmp,Pair[Momentum[x,___],Momentum[x,___]]|FeynAmpDenominator[PropagatorDenominator[Momentum[x,___],___]]]||(!FreeQ[tmp,pp]),
	Print["Check the input!"];Abort[]];
	
ttmp=Collect[Expand[tmp],Pair[Momentum[x,___],LorentzIndex[___]]];
If[!FreeQ[ttmp,Power[Pair[Momentum[x,___],LorentzIndex[___]],___]],tmp=Contract[ttmp]];
(* Contract x_mu x^mu *)
(*//////////////////// deal with input //////////////////////*)

If[!FreeQ[tmp,DiracGamma]||!FreeQ[tmp,Eps],tmp=Uncontract[DiracGammaExpand[tmp],x]];
(* expand lorentz contarction related to x :  \[Epsilon]^\[Mu]\[Nu]xz \[Rule] \[Epsilon]^\[Mu]\[Nu]\[Alpha]z x_\[Alpha]  ;  \[Gamma](x+z) \[Rule] \[Gamma]x +\[Gamma]z , \[Gamma]x \[Rule] \[Gamma]^\[Mu] x_\[Mu]] *)

If[!FreeQ[tmp,Times[_DiracGamma,Pair[Momentum[x,___],LorentzIndex[_,___]]]],

	tmp=tmp//.{h___.Plus[others__,Times[g_DiracGamma,vector_]].l___:>h.Plus[others].l+h.g.l vector
	,h___.Times[g_DiracGamma,vector_].l___:>h.g.l vector}
];(* separate \[Gamma]^\[Mu] x_\[Mu] :  \[Gamma].(\[Gamma]^\[Mu] x_\[Mu] + \[Gamma]z + \[Gamma] )...  ->  x_\[Mu] \[Gamma].\[Gamma]^\[Mu] ... + \[Gamma].(\[Gamma]z + \[Gamma])... *)

(*-------------------------------------------*)
If[!FreeQ[tmp,FeynAmpDenominator],
	tmp=FeynAmpDenominatorSplit[tmp]/.FeynAmpDenominator[PropagatorDenominator[Momentum[x,dim___],mass_]]:>
	(If[mass!=0,Print["mass in denorminator will be ignore!"]];1/Pair[Momentum[x,dim],Momentum[x,dim]])
];(* FAD[x] \[Rule] 1/SPD[x] *)


test=tmp//.Pair[Momentum[x,dim___],Momentum[l_,dim___]]^power_Integer?Negative/;ToString[l]!=ToString[x]:>wrong[x,l];
If[!FreeQ[test,wrong[__]],
Print["some scalar product involve external vector have negative power as: 
\[Integral]\!\(\*SuperscriptBox[\(d\), \(4\)]\)x \!\(\*FractionBox[\(1\), SuperscriptBox[\((xz)\), \(n\)]]\)\!\(\*SuperscriptBox[\(e\), \(ipx\)]\)         ( n > 0 )
 FourierXP/PX can't deal with this"];Abort[]];(* it's hard to handl with (xz)^(-n), give up the calculation *)


tmp=ExpandScalarProduct[tmp,Momentum->x];(* (z+x)x ... \[Rule] zx + x^2 ...*)

If[!FreeQ[tmp,Pair[Momentum[x,___],Momentum[__]]],

	tmp=tmp//.Pair[Momentum[x,dim___],Momentum[l_,dim___]]^power_Integer?Positive/;ToString[l]!=ToString[x]:>Apply[times,Table[Pair[Momentum[x,dim],Momentum[l,dim]],{i,power}]];

	tmp=tmp//.Pair[Momentum[l_,dim___],Momentum[x,dim___]]/;ToString[l]!=ToString[x]:>(li=LorentzIndex[$AL[Unique[]],dim];Pair[li,Momentum[l,dim]] Pair[li,Momentum[x,dim]]);
	tmp=tmp/.times->Times;
	
];(* uncontract scaler product related to x :  xz \[Rule] x^\[Mu] z_\[Mu]; (xz)^n \[Rule] x^\[Mu] z_\[Mu]  x^\[Nu] z_\[Nu]... *)

(*---------------------------------------------*)



If[!FreeQ[tmp,Momentum[x]]&&!FreeQ[tmp,Momentum[x,_]],
	Print["Dimension of ",x," inconsistent!"];Abort[],
	If[FreeQ[tmp,Momentum[x,_]], mdim=4,  tmp/.Momentum[x,dim_]:>(mdim=dim;1)]
];(*check and get dimension *)

tmp = null2 nulllo[nullindx]Pair[Momentum[x,mdim],Momentum[x,mdim]]^null5(null1/Pair[Momentum[x,mdim],Momentum[x,mdim]] + tmp);(* to avoid discuss the form of tmp *)

(* Expand and collect x ; add null3 to avoid Mathematica take (-1)^(D/2) as i^D *)
tmp = Expand[tmp,Pair[_,Momentum[x,___]]]/.Power[factor_ Pair[Momentum[x,dim___],Momentum[x,dim___]],power_]:>
	If[FreeQ[factor,-1],factor^power,(-1)^Quotient[4(power/.D->0),4]I^(Quotient[Mod[4(power/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[power-(power/.D->0)+Mod[Mod[4power/.D->0,4],2]/4]]] (-factor)^power]  Pair[Momentum[x,dim],Momentum[x,dim]]^power;

tmp=tmp//.{nulllo[lo___]Pair[Momentum[x,din___],LorentzIndex[lor_,din___]]:>nulllo[lo,lor],Power[Pair[Momentum[x,din___],Momentum[x,din___]],por___]:>nullpo[por]};

tmp=Collect[tmp,nulllo[___]nullpo[___]];


(*///////////////// fourier transform term by term //////////////////*)
(* seprate lorentz struct involved in Fourier transform and other terms, since many terms have same dimension and length of lorentx indeices,
 so generate Fourier transformation for terms with different dimension and length of lorentx indeices, then raplace lorentz indices *)

tmp=If[Head[tmp]=!=Plus,{tmp},Replace[tmp,Plus->List,{1},Heads->True]];

lorindx=tmp/.nullpo[aa_]nulllo[bb___,nullindx,cc___]___:>{aa/.null5->0,{bb,cc}};

Flist=DeleteDuplicates[Replace[lorindx,{bb___}:>Length[{bb}],{2}]];
If[ToString[OptionValue[Dimension]]=="AsIs",di=mdim,di=OptionValue[Dimension]];

Flist=Replace[Flist,{aa_,bb_}:>{aa,bb,getfourier[aa,bb,x,p,di,mdim,inverse]},{1}];

tmp=tmp/.nullpo[___]nulllo[___]other_:>other;


For[i=1,i<Length[tmp]+1,i++,
null5=Flist/.{lorindx[[i,1]],Length[lorindx[[i,2]]],c_}:>(tempresult=c;1);
lorindx[[i]]=tempresult[[2]]/.Thread[Rule[tempresult[[1]],lorindx[[i,2]]]];
];


result=lorindx tmp;


result=Collect[Collect[result,I],(-1)^_]/.nullIdentity[aa_]nullIdentity[bb_]:>nullIdentity[aa bb];
result=result/.(-1)^nullIdentity[aa_](-1)^nullIdentity[bb_]:>(-1)^Quotient[4((aa+bb)/.D->0),4]I^(Quotient[Mod[4((aa+bb)/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[aa+bb-((aa+bb)/.D->0)+Mod[Mod[4(aa+bb)/.D->0,4],2]/4]]];
result=Collect[result,(-1)^_];
result=result/.(-1)^aa_ (-1)^nullIdentity[bb_]:>(-1)^Quotient[4((aa+bb)/.D->0),4]I^(Quotient[Mod[4((aa+bb)/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[aa+bb-((aa+bb)/.D->0)+Mod[Mod[4(aa+bb)/.D->0,4],2]/4]]];
result=result/.I I^aa_:>(-1)^Quotient[4(((aa+1)/2)/.D->0),4]I^(Quotient[Mod[4(9((aa+1)/2)/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[(aa+1)/2-(((aa+1)/2)/.D->0)+Mod[Mod[4((aa+1)/2)/.D->0,4],2]/4]]];
result=result/.I^aa_:>(-1)^Quotient[4((aa/2)/.D->0),4]I^(Quotient[Mod[4((aa/2)/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[aa/2-((aa/2)/.D->0)+Mod[Mod[4((aa/2))/.D->0,4],2]/4]]];
result=Replace[result//Total,List->Identity,{1},Heads->True];

result=result/.{null1->0,null2->1,null3->Identity,nullIdentity->Identity,p:>pp};


If[opt==Integer, result=result/.Qamm[nn_Integer]/;nn<4 :>Gamma[nn]];

If[opt==All,result=result/.Qamm:>Qamma];

result
]






(* ------------------------------------------------------------------------- *)

getfourier[d_,n_,x_,p_,di_,mdim_,inver_]:=Block[{findex=-d,dindex={},sign,factor,fco,f,co1,co2,null3,tmp,ii,jj,res},
If[inver==True,sign=1;factor=(2Pi)^(-di)];
If[d==0,Print["terms with no ",SuperscriptBox[x,2]//DisplayForm," involved, please make sure the input is correct!"]];

co2=(-1)^Quotient[4((-di/2+findex)/.D->0),4]I^(Quotient[Mod[4((-di/2+findex)/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[(-di/2+findex)-((-di/2+findex)/.D->0)+Mod[Mod[4((-di/2+findex))/.D->0 ,4],2]/4]]];
co1=(-1)^Quotient[4((findex+1/2)/.D->0),4]I^(Quotient[Mod[4((findex+1/2)/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[(findex+1/2)-((findex+1/2)/.D->0)+Mod[Mod[4((findex+1/2))/.D->0 ,4],2]/4]]];

fco=sign factor co1 2^(di-2findex) Pi^(di/2) Qamm[di/2 - findex]/Qamm[findex];
f=co2 Pair[Momentum[p,mdim],Momentum[p,mdim]]^null3[-di/2+findex];
(* for findex\[GreaterEqual] 0 it get 0 because 1/Gamma[n](n\[LessEqual]0) = 0 *)


If[n=!=0,
(* if n\[NotEqual]0, derivative is needed *)
dindex=Table[$AL[Unique[]],{ii,1,n}];

	For[jj=1, jj<n+1, jj++,
			f = sign I FourDivergence[f, Pair[LorentzIndex[dindex[[jj]],mdim],Momentum[p,mdim]]];
			f = f/.{Times[null3[xx_]+yy_,zz__]:> -zz Qamm[-xx-yy+1]/Qamm[-xx-yy],Times[null3[xx_],zz__]:> -zz Qamm[-xx +1]/Qamm[-xx]}
	]
(* derivative; simplify the factor generated by derivative to Qamm[]/Qamm[], sometime e.g. (D-4)Qamm[D-4] = Qamm[D-3], but if set D=4 first, it = 0 since Qamm[] is just a symbol *)
];


res={dindex,Simplify[fco*f]/.null3->Identity,unllIdentity->Identity}(* here must simplify Qamm[], to avoid terms like Qamm[0](x/Qamm[0]), which may get error *)


];


(*FourierPX is just FourierXP[...,Inverse\[Rule]True] *)

FourierPX[expr_,{x_,p_},OptionsPattern[]]:=Block[{option=OptionValue[TrueGamma],dim=OptionValue[Dimension]},

FourierXP[expr,{x,p},TrueGamma->option,Dimension->dim,Inverse->True]
]




IntegrateLog[expr_,{s_,sl_,su_},opt:OptionsPattern[]]:=Block[{opt2,opt3,limit,tmp,liml=0,limu=0},
opt2={opt};

limit=If[FilterRules[{opt2},Limit]=={},"Auto",FilterRules[{opt2},Limit][[1,2]]];
opt3=FilterRules[{opt2},Except[{Limit,GeneratedParameters,PrincipalValue,Direction}]];
opt2=FilterRules[{opt2},Except[{Limit,Direction,Method,PerformanceGoal}]];


If[ToString[sl]==ToString[su],
0,
tmp=IntegrateLog[expr,s,#]&@opt2;

If[(Length[limit]==2)&&NumberQ[limit[[1]]]&&NumberQ[limit[[2]]],
(Limit[tmp,s->su,Direction->limit[[2]],#]&@opt3) -(Limit[tmp,s->sl,Direction->limit[[1]],#]&@opt3)
,


If[ToLowerCase[ToString[limit]]=="auto",
(* sl for lower bound, su for up bound. the direction of limit is seted to approach the integral bound, if at least one of sl and su is a specified number of infinity.
  and the direction of integral is supposed:
  for sl and su are speficied number, along the direction sl\[Rule]su
  for one speficied real number, along the direction - \[Rule] +
 for one speficied comeplex number, along the direction 0->sl or 0->su, if sl or su is speficied
   for one infinity, along the direction sl \[Rule] 0 or 0 \[Rule] su, if |sl| or |su|=infinity
for |sl|=|su|=infinity and they differ by a sign, along the direction sl\[Rule]0\[Rule]su 
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
(Limit[tmp,s->su,#]&@opt3) -(Limit[tmp,s->sl,#]&@opt3)
,
(Limit[tmp,s->su,Direction->limu,#]&@opt3) -(Limit[tmp,s->sl,Direction->liml,#]&@opt3)
 ]
,
(tmp/.s->su) - (tmp/.s->sl)
]
]
]


]




IntegrateLog[expr_,x:Except[_?ListQ],opt:OptionsPattern[]]:=Block[
{tmp,tmp2,res,null,null0,null2,i=0,int,int2,log,log2,opt2},
opt2=FilterRules[{opt},Except[{Limit,Direction,Method,PerformanceGoal}]];

tmp=Replace[ExpandAll[null(null0+expr)],{Log[z_]:>log2[z],Log[z_]^n_Integer/;n>0:>log2[z]^n},{2}];
(* null and null0 are set to unify the expression, so that only the polynomial of Log will be involved *)

tmp2=tmp/.log2[_]->0;(* seprate the terms Log not involved *)

tmp=int[tmp-tmp2]//.log2[t_]^n_:>(i+=1; log2[t]^(n-1) log2[null2[i] t]);(* Log^n \[Rule] Log * log * ... ; insert null2[i] to avoid Mathematica simplify these to Log^n*)

tmp=tmp//.int[c_]/;!FreeQ[c,log2] :>(c/.a_ log2[t_] :>int[null a]log[t]-int2[int[null a] D[t,x]/t]); (* intergal by part nutill no log2 *)

tmp=(tmp/.{null->1,null0->0,null2[_]->1,log->Log,log2->Log})//.{int[z_]:>Inactive[Integrate[z,x,#]&@opt2],int2[z_]:>Inactive[Integrate[z,x,#]&@opt2]};(* evaluate the integrate *)

res=Activate[tmp]+Integrate[tmp2/.{null->1,null0->0},x,#]&@opt2

]


QEvaluate[expr_,p_,OptionsPattern[]]:=Block[
{tmp,null,null1,null2,list,nullist,tmplist,log,plus,nlocal=True,ieps,ilog,dim=OptionValue[D],ldim=4,ldim2=4,ord=OptionValue[Order],i,j,scheme=OptionValue[Scheme]},

tmp=QDimension[expr,D->dim];(*see QDimension*)

If[FreeQ[tmp,Momentum[p,___]],
tmp
,
nullist=Cases[tmp,Momentum[_,dim___]|LorentzIndex[_,dim___]:>dim,Infinity]//DeleteDuplicates;(* check the dimension *)

If[Length[nullist]>1,
	Print["Dimension inconsistent!"];
	tmp=tmp/.{Momentum[x_,___]:>Momentum[x,D],LorentzIndex[x_,___]:>LorentzIndex[x,D]}
];


If[FreeQ[tmp,Epsilon],

	tmp=QGather[tmp,p]
,

	tmp=Expand[tmp];(* unify the form *)
	tmp=tmp/.{Power[Pair[Momentum[p,dim___],Momentum[p,dim___]],pow_]:>(-1)^(-pow)Power[-Pair[Momentum[p,dim],Momentum[p,dim]],pow],
			Power[a_ Pair[Momentum[p,dim___],Momentum[p,dim___]],pow_]:>(-1)^(-pow) a^pow Power[-Pair[Momentum[p,dim],Momentum[p,dim]],pow]};
		
				
	tmp=Series[tmp/.Qamm->Qamma,{Epsilon,0,ord}]//ExpandAll;
	
	
	
	list=Table[tmp[[3]][[i]] tmp[[1]]^(tmp[[4]]+i-1),{i,1,tmp[[5]]-tmp[[4]]}];(* a list of result like { O(1/\[Epsilon]^2), O(1/\[Epsilon]), O(0), ... } *)
							
	(* isolate Log[-p^2/4\[Pi]\[Mu]^2] for later Simplify *)
	list=list/.{Log[k_ Pair[Momentum[p,dim___],Momentum[p,dim___]]]:>
		If[ToLowerCase[ToString[scheme]]=="msbar",
			log[-SPD[p]/(ScaleMu^2)] +Log[-k]+2 Log[2]+ 2 Log[ScaleMu]+Log[Pi]-EulerGamma,
			log[-SPD[p]/(4 Pi ScaleMu^2)]+Log[-k]+2 Log[2]+2 Log[ScaleMu]+Log[Pi]],
			
			Log[Pair[Momentum[p,dim___],Momentum[p,dim___]]]:>
		If[ToLowerCase[ToString[scheme]]=="msbar",
			log[-SPD[p]/(ScaleMu^2)] + Pi I +2 Log[2]+ 2 Log[ScaleMu]+Log[Pi]-EulerGamma,
			log[-SPD[p]/(4 Pi ScaleMu^2)]+ Pi I +2 Log[2]+2 Log[ScaleMu]+Log[Pi]]};
		
		
	list=list/.{Log[xx_]:>PowerExpand[Log[xx]] ,  Power[Log[xx_],yy_]:>PowerExpand[Log[xx]]^yy};
	
	
	(*  MTD[a,b]\[Rule] MTD[a,b] + FVD[p,a]FVD[p,b]/SPD[p], then MTD[a,b]\[Rule] MTD[a,b]- FVD[p,a]FVD[p,b]/SPD[p] in the end *)
	If[!FreeQ[list,Pair[LorentzIndex[__],LorentzIndex[__]]],

		list=list/.Pair[LorentzIndex[x_,dim___],LorentzIndex[y_,dim___]]:>
				null1[x,y] null2 Pair[LorentzIndex[x,dim],LorentzIndex[y,dim]]+Pair[Momentum[p,dim],LorentzIndex[x,dim]]Pair[Momentum[p,dim],LorentzIndex[y,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]]
		];
	
	(* check non-local pole *)
	tmplist=list/.{Power[Epsilon,_?Negative]->ieps,log[__]->ilog};				
	If[!FreeQ[ExpandAll[tmplist],ieps ilog], nlocal=False];

	list=Collect[ExpandAll[list],Epsilon]/.log->Log;
	
	
	(* discard \[Epsilon] pole if non-local pole not involved *)
	If[(ToLowerCase[ToString[scheme]]=="ms")||(ToLowerCase[ToString[scheme]]=="msbar")&&nlocal,
		list=list/.Power[Epsilon,_?Negative]->0];
		
	For[i=1,i<Length[list]+1,i++,
		list[[i]]=Collect[#,null2]&/@(CoefficientList[list[[i]],null1[___]]//Simplify)
	];
		
		
	tmp=Total[Total[list]]/.{null2->1,Pair[LorentzIndex[x_,dim___],LorentzIndex[y_,dim___]]:>
				Pair[LorentzIndex[x,dim],LorentzIndex[y,dim]]-Pair[Momentum[p,dim],LorentzIndex[x,dim]]Pair[Momentum[p,dim],LorentzIndex[y,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]],null1[___]->1}
	
]
]
]





QGather[expr_,p_,OptionsPattern[]]:=Block[
{tmp,tmplor,tmpcoe,tmprem,tmp0,list={},log,null,null1,null0,i,n={},l,nn,m,k,ldim,lorentzIndex,tf=OptionValue[Table],separate=OptionValue[SeparateTransverse],subtract=OptionValue[Subtract]},
tmp=expr//FCI;

If[FreeQ[tmp,Momentum[p,___]],Print["Check input!"];Abort[]];
(* check the number of Lorentz index *)
tmp=tmp//.{Eps[x___,LorentzIndex[lo__],y___]:>null Eps[x,lorentzIndex[lo],y],Pair[LorentzIndex[lo__],mom_]:>null Pair[lorentzIndex[lo],mom]};

n=If[Length[Exponent[tmp,null,List]]!=1,Print["Lorentz structure inconsistent!"];Abort[]
	,Exponent[tmp,null,List][[1]]];
	
tmp=tmp/.{lorentzIndex->LorentzIndex,null->1};

tmp=tmp/.Log[x_]/;FreeQ[x,Pair]:>PowerExpand[Log[x]];
tmp=tmp/.Log[Pair[Momentum[p,dim___],Momentum[p,dim___]]]:>log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(4\[Pi] ScaleMu^2)]+2 Log[2]+Log[Pi]+2 Log[ScaleMu]+ Pi I;
tmp=tmp/.Log[a_ Pair[Momentum[p,dim___],Momentum[p,dim___]]]:>log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(4\[Pi] ScaleMu^2)]+2 Log[2]+Log[Pi]+2 Log[ScaleMu]+ PowerExpand[Log[-a]];
tmp=tmp/.Log[a_ Power[Pair[Momentum[p,dim___],Momentum[p,dim___]],-1]]:>-log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(4\[Pi] ScaleMu^2)]-2 Log[2]-Log[Pi]-2 Log[ScaleMu]+ PowerExpand[Log[-a]];

If[ToLowerCase[ToString[subtract]]=="msbar",
	tmp=tmp/.log[a_ Pair[Momentum[p,dim___],Momentum[p,dim___]]]:>log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(ScaleMu^2)]+2 Log[2]+Log[Pi]+2 Log[ScaleMu]+ PowerExpand[Log[-a]]-EulerGamma;
	tmp=tmp/.log[a_ Power[Pair[Momentum[p,dim___],Momentum[p,dim___]],-1]]:>-log[-Pair[Momentum[p,dim],Momentum[p,dim]]/(ScaleMu^2)]-2 Log[2]-Log[Pi]-2 Log[ScaleMu]+ PowerExpand[Log[-a]]+EulerGamma
	];

tmp=tmp/.Log[a_]:>PowerExpand[Log[a]];


(* to separate transverse and longitudinal part,
first MTD[a,b]\[Rule] MTD[a,b] + FVD[p,a]FVD[p,b]/SPD[p], then MTD[a,b]\[Rule] MTD[a,b]- FVD[p,a]FVD[p,b]/SPD[p] in the end *)
If[separate==True,tmp=tmp/.Pair[LorentzIndex[a_,dim___],LorentzIndex[b_,dim___]]:>
			Pair[LorentzIndex[a,dim],LorentzIndex[b,dim]]+Pair[Momentum[p,dim],LorentzIndex[a,dim]]Pair[Momentum[p,dim],LorentzIndex[b,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]]];

(* gather to a list *)
If[n>0,
	tmp=tmp//ExpandAll;

(* //////// get the terms have same Lorentz structure with first term //////////*)
	While[Head[tmp]===Plus,
		tmpcoe=tmp[[1]]/.{Eps[__]:>1,Pair[LorentzIndex[__],_]:>1};
		tmplor=tmp[[1]]/tmpcoe;

		tmprem=tmp/.tmplor:>0;
		tmp0=tmp-tmprem/.{Eps[__]:>1,Pair[LorentzIndex[__],_]:>1};

		tmp=tmprem;
		list=Append[list,{tmplor,tmp0}]
		];

	If[tmp=!=0,
		tmpcoe=tmp/.{Eps[__]:>1,Pair[LorentzIndex[__],_]:>1};
		tmplor=tmp/tmpcoe;
		list=Append[list,{tmplor,tmpcoe}]
		];
,

	list={{1,tmp}}
];

For[l=1,l<Length[list]+1,l++,
	list[[l,2]]= CoefficientList[list[[l,2]],1/Epsilon];
	nn=Length[list[[l,2]]];
	list[[l,2]]=Reverse[list[[l,2]]Table[Epsilon^(-k),{k,0,nn-1}]];
	];

(* gathe longitude part and transverse part*)
If[separate==True,list=list/.Pair[LorentzIndex[a_,dim___],LorentzIndex[b_,dim___]]:>
			Pair[LorentzIndex[a,dim],LorentzIndex[b,dim]]-Pair[Momentum[p,dim],LorentzIndex[a,dim]]Pair[Momentum[p,dim],LorentzIndex[b,dim]]/Pair[Momentum[p,dim],Momentum[p,dim]]];


(*-----------------------*)
If[((ToLowerCase[ToString[subtract]]=="ms")||(ToLowerCase[ToString[subtract]]=="msbar")) && 
	FreeQ[list//Expand,log[___]Power[Epsilon,_?Negative]]&&FreeQ[list//Expand,Power[log[___],___]Power[Epsilon,_?Negative]],
	list=list/.Power[Epsilon,_?Negative]->0;
	list=list//.{0,b___}:>{b} ];


If[tf==True,
  For[i=1,i<Length[list]+1,i++,
      list[[i,2]]=Simplify[list[[i,2]]]];
  tmp=list,
  
	(* add null1 to isolate Epsilon and other terms to avoid expand them *)
	list=Collect[Epsilon^null0 list,Epsilon]/. a_ Power[Epsilon,b_]:>null1[a//Simplify]Power[Epsilon,b - null0];
	tmp=Total[#]&/@list[[;;,2]];
	tmp=Collect[Total[tmp list[[;;,1]]],Epsilon]/.null0->0;
	
];

tmp/.{null1->Identity,log->Log}

]




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



If[!FreeQ[tmp,Pair[LorentzIndex[__],Momentum[__]]]||!FreeQ[Eps[___,Momentum[__]]],
Print["Lorentz vector involed, the result may not desired. consider use QGather first"]
];

(*///////////////////////////////////////////////////*)

If[disp,
(* act Borel transformation on dispersion integral *)
(* \[PartialD]^n f(t) = n!/(2\[Pi]I) \[Integral] ds f(s)/(s-t)^(n+1)*)

s=If[Length[factor]!=3,Print["check the input!"];Abort[],factor[[3]]];
tmp=tmp/.Pair[Momentum[p,___],Momentum[p,___]]->s;


tmp=If[im,
tmp=ExpandAll[tmp/.{Log[-1x__]:>Log[Times[x]]-I Pi,Log[Rational[-1,y_]x__]:>Log[1/y Times[x]]-I Pi}];
tmp=tmp-(tmp/.Complex[_,_]->0);
tmp=tmp/.{tt__ Complex[rr_,ii_]:> tt ii,Complex[rr_,ii_]:>ii},

tmp];

tmpr=t^(deriv+1) Exp[-s t]tmp

,
(*/////////////////////////////////////////////////*)
(* act Borel transformation directly *)
If[im,
(*tmp=ExpandAll[tmp/.{Log[-1x__]:>Log[Times[x]]-I Pi,Log[Rational[-1,y_]x__]:>Log[1/y Times[x]]-I Pi}];*)

tmp=tmp-(tmp/.Complex[_,_]->0);
tmp=tmp/.{tt__ Complex[rr_,ii_]:> tt ii,Complex[rr_,ii_]:>ii}
];(* subtract pure real term; get the imaginary part *)

If[deriv>0,tmp=D[tmp/.Pair[Momentum[p,___],Momentum[p,___]]:>Pair[Momentum[p,D],Momentum[p,D]],
{Pair[Momentum[p,D],Momentum[p,D]],deriv}]];(* derivate *)

If[sub>0,tmp=tmp/(Pair[Momentum[p,D],Momentum[p,D]]^sub)];(* subtractions in dispersion integral *)

(* get the power of p^2 and Log[-p^2] *)
tmp=tmp/.{Pair[Momentum[p,___],Momentum[p,___]]:>a,Log[y___ Pair[Momentum[p,___],Momentum[p,___]]]:>b Log[bb Times[y]]};


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


If[xx>=0&&yy==1,tmpr=tmpr-tmp[[i]]/.Log[bb y___]:>Gamma[xx+1] t^(-xx)];

If[xx>=0&&yy==2,tmpr=tmpr+tmp[[i]]/.Log[bb y___]:>2Gamma[xx+1]t^(-xx) (1/t -Sum[1/j,{j,1,xx}])];


If[xx<0&&yy==1,tmpr=tmpr+tmp[[i]]/.Log[bb y___]:>((-1)^(-xx)t^(-xx) (-Log[-t/Times[y]]+PolyGamma[-xx])/Gamma[-xx])];

If[xx<0&&yy==2,tmpr=tmpr+tmp[[i]]/.Log[bb y___]^2:>((-1)^(-xx)t^(-xx)  (Log[-t/Times[y]]^2-2PolyGamma[-xx]Log[-t/Times[y]]+PolyGamma[-xx]^2 -PolyGamma[1,-xx])/Gamma[-xx])];

];

tmpr=tmpr/.{a->1,b->1}
];


1/t tmpr//Simplify

]





(*           \[Integral]d^D x 
1. spreate to different denominator 
	tmp2 = tmp[[i]]
	
	. once the power indices getted, set denominator to 1

2. for every term have same denominator, seprate numerator to different number of vector x^\[Mu]
	tmp3 = tmp2[[j]]

3. for every numerator have same number of vectors, it may have different Lorentz indices on it
	 replace x^\[Mu] x^\[Nu] ...  to C(x^2)^n g^\[Mu]\[Nu] g^\[Rho]\[Sigma] ...
	 e.g.  ( x^\[Mu] x^\[Nu] z^\[Rho] + x^\[Nu] x^\[Rho] z^\[Mu] ) \[Rule] 1/D x^2(g^\[Mu]\[Nu] z^\[Rho] + g^\[Nu]\[Rho] z^\[Mu])
	tmp4 = tmp3[[k]]
	
	. once the number of vectors getted, set x^\[Mu] to 1 and get the list of Lorentz indices
	
4. get the integral result, according to the power indices, the number of vectors x^\[Mu], the power of feynman paramaters 
*)





Qdx[expr_,x_,OptionsPattern[]]:=Block[
{ttm,tmp,result=0,list,listlor,tmplist,glist,g,tmpg,i=1,j=1,n=1,k=1,null0,null1,null2,null5,nullx,tempresult,nullpo,nullpo2,nulllo,nulllo2,nullindx,lorindx,Ilist,
li,times,plus,mdim,momentum,test,wrong,pair,tttmp,rulem11,rulem12,idp=OptionValue[dp]},


tmp=(Contract[expr]//FCI)//Expand;

(* extract commutate part from none-commutate \[Gamma] struct *)
tmp=tmp//.a___.(b_+c_).d___:>a.b.d+a.c.d;
tmp=tmp//.a___.(-1b_).d___:> -a.b.d;
tmp=tmp//.a___.(Pair[Momentum[b_,dim___],Momentum[b_,dim___]] c_).d___:>Pair[Momentum[b,dim],Momentum[b,dim]]a.c.d;
tmp=tmp//.a___.(Power[Pair[Momentum[b_,dim___],Momentum[b_,dim___]],e_] c_).d___:>Power[Pair[Momentum[b,dim],Momentum[b,dim]],e]a.c.d;
tmp=tmp//.a___.(b_+c_).d___:>a.b.d+a.c.d;
tmp=tmp//.a___.(-1b_).d___:> -a.b.d;

(*  check the dimension *)
If[!FreeQ[tmp,Momentum[x]|Momentum[x+__]|Momentum[__-x]],
	Print["Dimension of ",x," will be set to D!"]];

(* massless check *)
If[!FreeQ[tmp,PropagatorDenominator[Momentum[x|x+__|__ -x,___],mass_/;ToString[mass]!="0"]],
	Print["mass involved!"];Abort[]];

(* ----------------- deal with input ------------------*)


If[!FreeQ[tmp,FeynAmpDenominator],
	tmp=FeynAmpDenominatorSplit[tmp]/.{FeynAmpDenominator[PropagatorDenominator[Momentum[x|x+z__,dim___],mass_]]:>
	1/Pair[Momentum[x+z,dim],Momentum[x+z,dim]],
	FeynAmpDenominator[PropagatorDenominator[Momentum[z__-x,dim___],mass_]]:>
	1/Pair[Momentum[x-z,dim],Momentum[x-z,dim]],
	FeynAmpDenominator[PropagatorDenominator[Momentum[x,dim___] + Momentum[z_,dim___],mass_]]:>
	1/Pair[Momentum[x+ z,dim],Momentum[ x+ z,dim]],
	FeynAmpDenominator[PropagatorDenominator[aa_ Momentum[x,dim___] + Momentum[z_,dim___],mass_]]:>
	1/Pair[Momentum[aa x+ z,dim],Momentum[aa x+ z,dim]],
	FeynAmpDenominator[PropagatorDenominator[Momentum[x,dim___] + bb_ Momentum[z_,dim___],mass_]]:>
	1/Pair[Momentum[x+bb z,dim],Momentum[x+bb z,dim]],
	FeynAmpDenominator[PropagatorDenominator[aa_ Momentum[x,dim___] + bb_ Momentum[z_,dim___],mass_]]:>
	1/Pair[Momentum[aa x+bb z,dim],Momentum[aa x+bb z,dim]]}
];(* FAD[x] \[Rule] 1/SPD[x] *)



If[FreeQ[tmp,Pair[Momentum[x,___],Momentum[x,___]]|Pair[Momentum[x+_,___],Momentum[x+_,___]]|Pair[Momentum[-x+_,___],Momentum[-x+_,___]]]&&(tmp=!=0),
	Print["Check the input [f[x],{x,p}] "];Abort[]];
	
	
(* unify the form *)
tmp=tmp/.{Power[(Pair[Momentum[x,dim___],Momentum[x,dim___]]+Pair[Momentum[e_,dim___],Momentum[e_,dim___]]
					+a_ Pair[Momentum[x,dim___],Momentum[e_,dim___]]),pindx_]/;(Abs[a]==2):>
			Pair[Momentum[x+a/2 e,dim],Momentum[x+a/2 e,dim]]^pindx,
			Power[(-Pair[Momentum[x,dim___],Momentum[x,dim___]]-Pair[Momentum[e_,dim___],Momentum[e_,dim___]]
					+a_ Pair[Momentum[x,dim___],Momentum[e_,dim___]]),pindx_]/;(Abs[a]==2):>
			(-Pair[Momentum[x-a/2 e,dim],Momentum[x-a/2 e,dim]])^pindx};


tmp=tmp/.Pair[Momentum[z_-x,dim___],Momentum[z_-x,dim___]]:>Pair[Momentum[x-z,dim],Momentum[x-z,dim]];

(* ---------- ((c x^2)^n) \[Rule] c^n ((x^2)^n) ----------------- *)
(* avoid mathematica take (-1)^(-1/2 D) as i^D, simplify (-1)^n since there are many term donly differ bu a sign*)
tmp=tmp/.{Power[factor__ Pair[Momentum[x+z__,dim___],Momentum[x+z__,dim___]],power__]:>
			If[FreeQ[factor,-1],factor^power,(-1)^Quotient[4(power/.D->0),4]I^(Quotient[Mod[4(power/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[power-(power/.D->0)+Mod[Mod[4(power)/.D->0,4],2]/4]]](-factor)^power] Pair[Momentum[x+z,dim],Momentum[x+z,dim]]^power,	
			Power[factor__ Pair[Momentum[x,dim___],Momentum[x,dim___]],power__]:>
			If[FreeQ[factor,-1],factor^power,(-1)^Quotient[4(power/.D->0),4]I^(Quotient[Mod[4(power/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[power-(power/.D->0)+Mod[Mod[4(power)/.D->0,4],2]/4]]] (-factor)^power]  Pair[Momentum[x,dim],Momentum[x,dim]]^power};

tmp=tmp/.(-1)^aa_ (-1)^nullIdentity[bb_]:>(-1)^Quotient[4(aa+bb/.D->0),4]I^(Quotient[Mod[4(aa+bb/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[aa+bb-(aa+bb/.D->0)+Mod[Mod[4(aa+bb)/.D->0,4],2]/4]]];
tmp=tmp/.I I^aa_:>(-1)^Quotient[4((aa+1)/2/.D->0),4]I^(Quotient[Mod[4((aa+1)/2/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[(aa+1)/2-((aa+1)/2/.D->0)+Mod[Mod[4((aa+1)/2)/.D->0,4],2]/4]]];
tmp=tmp/.I^aa_:>(-1)^Quotient[4((aa)/2/.D->0),4]I^(Quotient[Mod[4((aa)/2/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[(aa)/2-((aa)/2/.D->0)+Mod[Mod[4((aa)/2)/.D->0,4],2]/4]]];

(* ------ stop when 1/(xz)^n involved ------*)
	
If[!FreeQ[tmp,Pair[Momentum[x,dim___],Momentum[l_,dim___]]^power_Integer?Negative /;ToString[l]!=ToString[x]],
	Print[" 1/(",x,"z)^n type of input involved, current version can't deal with this!"];
	Abort[]];



(* get denominator, expand numerator *)
tmp=tmp//Expand;
(*-----------------------------------------------------------------------------------------------------------------------------------------------------------------------*)

tmp=tmp nulllo[{nullindx}]+null0+null0^2//Expand;


tmp=(# nullpo[Cases[#,Pair[Momentum[xx_,___],Momentum[xx_,___]]^p_Integer?Negative /;!FreeQ[xx,x]:>{xx-x,-p},Infinity]])&/@tmp;
tmp=(# nullpo[Cases[#,Pair[Momentum[xx_,___],Momentum[xx_,___]]^p_/;(!FreeQ[xx,x])&&(!FreeQ[p,D]):>{xx-x,-p},Infinity]])&/@tmp;
tmp=tmp/.{Pair[Momentum[xx_,___],Momentum[xx_,___]]^p_Integer?Negative /;!FreeQ[xx,x]->1,Pair[Momentum[xx_,___],Momentum[xx_,___]]^p_/;(!FreeQ[xx,x])&&(!FreeQ[p,D])->1};

tmp=(# nullpo2[Cases[#,nullpo[{aa___}]:>aa,Infinity]])&/@tmp;

If[!FreeQ[tmp,nullpo2[aa_]/;Length[aa]>2],Print["Sorry! the current version can't deal with this!"];Abort[]];
tmp=tmp/.nullpo2[aa_]/;Length[aa]==1 -> 0;
tmp=tmp/.nullpo[___]->1;

tmp=qExpand[tmp,x,lessdummy->OptionValue[lessdummy]];


tmp=tmp/.Power[Pair[Momentum[xx_,dim___],LorentzIndex[lor_,dim___]],2]/;!FreeQ[xx,x]:>Pair[Momentum[xx,dim],LorentzIndex[lor,dim]]Pair[Momentum[xx+nullx,dim],LorentzIndex[lor,dim]];
tmp=(# nulllo[Cases[#,Pair[Momentum[xx_,___],LorentzIndex[lor_,___]]/;!FreeQ[xx,x]:>{xx,lor},Infinity]])&/@tmp;
tmp=tmp/.Pair[Momentum[xx_,___],LorentzIndex[lor_,___]]/;!FreeQ[xx,x]->1;

tmp=(# nulllo2[Cases[#,nulllo[{aa___}]:>aa,Infinity]])&/@tmp;
tmp=tmp/.{nulllo[___]->1,nullx->0};


tmp=tmp/.nulllo2[{nullindx}]->nulllo2[{{1,1}}];
tmp=tmp/.nulllo2[{aa___,nullindx,bb___}]:>nulllo2[{aa,bb}];
tmp=tmp/.nullpo2[a_]:>nullpo2[a//.{aa___,{mo_,po1_},bb___,{mo_,po2_},cc___}:>{aa,{mo,po1+po2//Expand},bb,cc}];


(*-----------------------*)

tmp=(tmp//Expand)/.null0->0;
If[tmp=!=0,

tmp=Collect[tmp,nullpo2[___]nulllo2[___]];

tmp=If[Head[tmp]=!=Plus,
	{tmp},
	Replace[tmp,Plus->List,{1},Heads->True]
	];
	
If[OptionValue[Simplify],tmp=Replace[#,Plus[a_+b_]:>Simplify[a+b],{2}]&/@tmp ];



tmp=tmp/.{nulllo2[cc__]:>nulllo2[cc//.{dd___,{aa1_,bb1_},{aa2_,bb2_},gg___}/;((ToString[aa1]!=ToString[aa2])&&(!FreeQ[{dd},{aa2,___}])):>{dd,{aa2,bb2},{aa1,bb1},gg}]};
		
lorindx=tmp/.nullpo2[aa_]nulllo2[cc_]other___:>{aa,Transpose[cc]};(* sort the lorentz structure *)
tmp=tmp/.{nullpo2[___]->1,nulllo2[___]->1};

(*-----------------------------------------------------------------------------------------------------------------------------------------------------------------------*)



Ilist=DeleteDuplicates[Replace[lorindx,{aa_,{bb_,ind_}}:>{aa,bb},{1}]];

Ilist=Replace[Ilist,{aa_,bb_}:>{aa,bb,getintegral[aa,bb,x,idp]},{1}];



For[i=1,i<Length[tmp]+1,i++,
null5=Ilist/.{lorindx[[i,1]],lorindx[[i,2,1]],c_}:>(tempresult=c;1);
lorindx[[i]]=tempresult[[1]]/.Thread[Rule[tempresult[[2]],lorindx[[i,2,2]]]];
];


result=Collect[tmp lorindx,nullIdentity[___]]/.nullIdentity[a_]nullIdentity[b_]:>nullIdentity[a b];


result=result/.(-1)^nullIdentity[aa_](-1)^nullIdentity[bb_]:>(-1)^Quotient[4(aa+bb/.D->0),4]I^(Quotient[Mod[4(aa+bb/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[aa+bb-(aa+bb/.D->0)+Mod[Mod[4(aa+bb)/.D->0,4],2]/4]]];
result=result/.(-1)^(nullIdentity[aa_]+nullIdentity[bb_]):>(-1)^Quotient[4(aa+bb/.D->0),4]I^(Quotient[Mod[4(aa+bb/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[aa+bb-(aa+bb/.D->0)+Mod[Mod[4(aa+bb)/.D->0,4],2]/4]]];
result=Collect[result,(-1)^_];
result=result/.(-1)^aa_ (-1)^nullIdentity[bb_]:>(-1)^Quotient[4(aa+bb/.D->0),4]I^(Quotient[Mod[4(aa+bb/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[aa+bb-(aa+bb/.D->0)+Mod[Mod[4(aa+bb)/.D->0,4],2]/4]]];
result=result/.I I^aa_:>(-1)^Quotient[4((aa+1)/2/.D->0),4]I^(Quotient[Mod[4((aa+1)/2/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[(aa+1)/2-((aa+1)/2/.D->0)+Mod[Mod[4((aa+1)/2)/.D->0,4],2]/4]]];
result=result/.I^aa_:>(-1)^Quotient[4((aa)/2/.D->0),4]I^(Quotient[Mod[4((aa)/2/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[(aa)/2-((aa)/2/.D->0)+Mod[Mod[4((aa)/2)/.D->0,4],2]/4]]];
result=Replace[result//Total,List->Identity,{1},Heads->True];


result=result/.{null1->0,null2->1,nullIdentity->Identity,plus->Plus};


result=If[Length[null0+result/.{Qamm[1]->1,Qamm[2]->1,Qamm[3]->2}]==Length[result+null0],result/.{Qamm[1]->1,Qamm[2]->1,Qamm[3]->2},result];
(* if no potential problem, simplify small Gamma[n] *)

	If[ToLowerCase[ToString[OptionValue[Contract]]]=="true",
		result//Contract,
		result
		]
,
	0]

]


nullIdentity[];


qExpand[expr_,x_,OptionsPattern[]]:=Block[{tmp,tmp2,plus,times,li,null,dum=OptionValue[lessdummy],dumlist,dumlist2,dumlist3={},nn,maxlength,i=1,l1,l2,lorindx,momentum,pair,tmpl,tmpl2,tmpl3,tmpl4,reprule,lorentzIndex},

tmp=(expr//FCI)/.Power[Plus[a_+b_],c_?Negative]:>Power[plus[a,b],c];
tmp=tmp/.{Plus[a_+D]:>plus[a+D],Plus[a_-D]:>plus[a-D]};
tmp=ExpandAll[tmp];


(* extract commutate part from none-commutate \[Gamma] struct *)
tmp=tmp//.a___.(b_+c_).d___:>a.b.d+a.c.d;
tmp=tmp//.a___.(-1b_).d___:> -a.b.d;
tmp=tmp//.a___.(Pair[Momentum[b_,dim___],Momentum[b_,dim___]] c_).d___:>Pair[Momentum[b,dim],Momentum[b,dim]]a.c.d;
tmp=tmp//.a___.(Power[Pair[Momentum[b_,dim___],Momentum[b_,dim___]],e_] c_).d___:>Power[Pair[Momentum[b,dim],Momentum[b,dim]],e]a.c.d;
tmp=tmp//.a___.(b_+c_).d___:>a.b.d+a.c.d;
tmp=tmp//.a___.(-1b_).d___:> -a.b.d;



(* expand  x from dirac struct, epsilon tensor, \[Epsilon]^\[Mu]\[Nu]xz \[Rule] \[Epsilon]^\[Mu]\[Nu]\[Alpha]z x_\[Alpha] ,  \[Gamma](x+z) \[Rule] \[Gamma]^u (x+z)_u  *)
tmp=tmp/.Momentum[Plus[a_,b_],dim___]:>Momentum[plus[a,b],dim];
tmp=Uncontract[DiracGammaExpand[tmp],x];
tmp=tmp/.plus->Plus;



(* uncontract scaler product, xz \[Rule] x^\[Mu] z_\[Mu]; (xz)^n \[Rule] x^u z_u  x^v z_v... *)
tmp=tmp/.Power[xx_,power_Integer?Positive]/;!FreeQ[xx,Momentum[x,___]]:>Apply[times,Table[xx,{i,power}]];
(*tmp=tmp/.Pair[Momentum[x,dim___],Momentum[l_,dim___]]^power_Integer?Positive:>Apply[times,Table[Pair[Momentum[x,dim],Momentum[l,dim]],{i,power}]];*)

tmp=tmp/.Power[xx_,power_]/;!FreeQ[xx,Momentum[x,___]|Momentum[x+_,___]]:>Power[xx/.Momentum->momentum,power];(* avoid expand xy in denominator like (x^2+2xy +y^2)^(D-n) *)
tmp=tmp/.Pair[Momentum[l_,dim___],Momentum[xx_,dim___]]/;!FreeQ[xx,x]:>(li=LorentzIndex[$AL[Unique[]],dim];Pair[li,Momentum[l,dim]] Pair[li,Momentum[xx,dim]]);
	
tmp=tmp/.{times->Times,momentum->Momentum,null->0};



(* simplify dummy indices, since mathematica doesn't know x^u z_u = x^v z_v, which make the expresion very long sometime *)
If[dum&&(Head[tmp]===Plus),
	tmp=tmp//Expand;

	tmp=Replace[tmp,Plus->List,{1},Heads->True];
	
	tmp=tmp/.Pair[Momentum[xx_,dim___],LorentzIndex[lo_,dim___]]/;!FreeQ[xx,x]:>pair[Momentum[xx,dim],lorentzIndex[lo,dim]];
	
	tmpl=Cases[#,pair[Momentum[xx_,dim___],lorentzIndex[lo_,dim___]]/;!FreeQ[#,LorentzIndex[lo,___]]:>lo,Infinity]&/@tmp;
	tmpl=DeleteDuplicates[#]&/@tmpl;
	tmp=tmp/.{pair->Pair,lorentzIndex->LorentzIndex};
	
	tmpl4=Length[#]&/@tmpl;
	dumlist2=tmpl[[Position[tmpl4,Max[tmpl4]][[1]]  ]][[1]];
	
	tmp=MapThread[#1/.Thread[Rule[#2,dumlist2[[ 1;; Length[#2] ]] ] ]&,{tmp,tmpl}];
	
	tmp=tmp//Total
		
];
(*-----------------*)


tmp
]



getintegral[list_,nn_,x_,dp_]:=Block[{result=0,tmp,tmp3,tmp4,tmp5,tmpg,listlor,tmplist,lln=Length[nn],x1,x2,i=1,j=1,k=1,n=1,l=1,nnl,times,p1,p2,pp1,pp2,listlo,loo,null0,lloo,numerator,fpower,fmomentum,s1,s2,nx,momentum,co1,rule1},

fpower=list[[1,2]]+list[[2,2]];
fmomentum=list[[1,1]]-list[[2,1]];
x1=list[[1,1]];
x2=list[[2,1]];


If[ToString[nn]=="{1}",
numerator=1;
listlo={1}
,

listlo=Table[$AL[Unique[]],{i,1,lln}];
numerator=Product[Pair[Momentum[nn[[i]],D],LorentzIndex[listlo[[i]],D]],{i,1,lln}];

(* ------ shift x ; simplify: 1 - s1 \[Rule] s2; 1 - s2 \[Rule] s1 -------- *)
numerator=numerator/.x:>x-s1 x1-s2 x2;
(*rule1={xx_+s1 a_ /;!FreeQ[xx,-a]\[RuleDelayed]Expand[xx+(1-s2)a],  xx_+s2 a_ /;!FreeQ[xx,-a]\[RuleDelayed]Expand[xx+(1-s1)a],   xx_-s1 a_ /;!FreeQ[xx,a]\[RuleDelayed]Expand[xx-(1-s2)a],   xx_-s1 a_ /;!FreeQ[xx,a]\[RuleDelayed]Expand[xx-(1-s2)a]};*)
numerator=numerator/.Momentum[xx_,dim___]:>Momentum[short[xx,s1,s2],dim];


(* take s1 s2 out of the Momentum[] *)
numerator=numerator/.{Momentum[a_ + s1 b_+s2 c_,dim___]:>Momentum[a,dim]+s1 Momentum[b,dim]+s2 Momentum[c,dim],Momentum[a_ + s1 b_,dim___]:>Momentum[a,dim]+s1 Momentum[b,dim],  
		Momentum[a_ + s2 b_,dim___]:>Momentum[a,dim]+s2 Momentum[b,dim],Momentum[ s1 b_,dim___]:>s1 Momentum[b,dim],  Momentum[ s2 b_,dim___]:>s2 Momentum[b,dim]};

numerator=Expand[numerator//ExpandScalarProduct];
numerator=numerator/.{Pair[Momentum[-1 a_,dim___],LorentzIndex[lo_,dim___]] :> -Pair[Momentum[a,dim],LorentzIndex[lo,dim]],
				Pair[Momentum[nm_Integer a_,dim___],LorentzIndex[lo_,dim___]] :> nm Pair[Momentum[a,dim],LorentzIndex[lo,dim]]};

(* insert nx to account the number of x^\[Mu] *)
numerator=numerator//.Pair[LorentzIndex[lo__],Momentum[x,dim___]]:>nx Pair[LorentzIndex[lo],momentum[x,dim]];

numerator=numerator/.momentum->Momentum
];

numerator=MonomialList[Expand[nx numerator]/.nx^p_?EvenQ->0 ,{nx,s1,s2}];


(* --------------------- integrate term by term  -------------------------- *)
If[numerator=!={0},

For[j=1,j<Length[numerator]+1,j++,

tmp3=numerator[[j]];

p1=Exponent[tmp3,s1];
p2=Exponent[tmp3,s2];
n=(Exponent[tmp3,nx]-1)/2;

tmp3=Expand[tmp3]/.{nx->1,s1->1,s2->1};
tmp3=tmp3+null0;


(* ----- generate normalized symmetry tensor g[\[Mu],\[Nu],\[Rho],\[Sigma],...] ----- *)

k=1;
tmp5=0;
listlor={};

(* -------- x^\[Mu] x^\[Nu] \[Rule]  1/d x^2 g^\[Mu]\[Nu] ------- *)
For[k=1,k<Length[tmp3]+1,k++,
tmp4=tmp3[[k]];
tmp4=tmp4//.Pair[Momentum[x,___],LorentzIndex[lo_,___]]:>(listlor=Append[listlor,lo];1);
nnl=Length[listlor]/2;

listlor=listlor//.List[l1_,l2___]:>(l=1;tmpg=0;tmplist=List[l2];
			For[l=1,l<Length[tmplist]+1,l++,
			tmpg=tmpg + times[MTD[l1,tmplist[[1]]],tmplist[[2;;]]];
			tmplist=RotateLeft[tmplist]];
			tmpg);
	(* times normalization factor Qamm[D/2]/(2^n Qamm[D/2 +n]) later *)
listlor=(listlor/.{}->1)/.times->Times;

tmp5=tmp5+tmp4 listlor Qamm[D/2]/(2^nnl Qamm[D/2 +nnl]);(* factor from average *)
listlor={};
];

(* coefficients comes from x^0  \[Rule] -i x^0( p^0 \[Rule] i p^0 ), and integrate over x *)


If[dp,
pp1=fpower-n;
pp2=-fpower+n+D/2;
co1=(-1)^Quotient[4(pp1+pp2+1/2/.D->0),4]I^(Quotient[Mod[4(pp1+pp2+1/2/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[pp1+pp2-(pp1+pp2/.D->0)+Mod[Mod[4(pp1+pp2+1/2)/.D->0,4],2]/4]]](1/(2Pi)^D);

,
pp1= 1+fpower-n;
pp2= -fpower+n+D/2;
co1=(-1)^Quotient[4(pp1+pp2+1/2/.D->0),4]I^(Quotient[Mod[4(pp1+pp2+1/2/.D->0),4],2])nullIdentity[(-1)^nullIdentity[Expand[pp1+pp2-(pp1+pp2/.D->0)+Mod[Mod[4(pp1+pp2+1/2)/.D->0,4],2]/4]]];
];

tmp5=tmp5  co1 Pi^(D/2)  Qamm[fpower-n-D/2]Qamm[n+D/2]/(Qamm[fpower]Qamm[D/2])Pair[Momentum[fmomentum,D],Momentum[fmomentum,D]]^pp2 ;

(* the +- power in pp1 & pp2 is because, (-z^2)^D >>>wick rotation)>>> (-(-z'^2))^D = (z'^2)^D 
	so one -1 take out as (-1)^(-D), another -1 take out as (-1)^D *)

(* coefficients comes from feynman paramaterization, and integrate over parameter *)
tmp5=tmp5 Qamm[fpower]/(Qamm[list[[1,2]]]Qamm[list[[2,2]]]) Qamm[n+p1+D/2 -list[[2,2]] ]Qamm[n+p2+D/2 -list[[1,2]] ]/Qamm[2n+p1+p2+D-fpower];

result=result+(tmp5/.{null0->0})
];
];


result = { result/.{null0->0},listlo}
	];




short[expr_,a_,b_]:=Block[{i=1,j=1,k=1,list1,list2,list3,null1,null2,null3,tmp},
	
	list1=null1+(expr-(expr/.a->0))/.a->1;
	list2=null2+(expr-(expr/.b->0))/.b->1;
	list3=null3+(expr/.{a->0,b->0});

	For[i=1,i<Length[list3]+1,i++,
	tmp=list3[[i]];
	If[Length[tmp+list1]<Length[list1],list1=list1+tmp;list2=list2+tmp;list3=list3-tmp]
		];
	
	For[j=1,j<Length[list3]+1,j++,
	tmp=list3[[j]];
	If[Length[tmp+list2]<Length[list2],list1=list1+tmp;list2=list2+tmp;list3=list3-tmp]
		];
		
	For[k=1,k<Length[list1]+1,k++,
	tmp=list1[[k]];
	If[!FreeQ[list2,tmp],list3=list3+tmp;list1=list1-tmp;list2=list2-tmp]
		];
	(a list1+b list2 +list3)/.{null1->0,null2->0,null3->0}
	]


expandx[expr_,x_]:=Block[{tmp,times,li},
tmp=expr;
tmp=ExpandScalarProduct[tmp,Momentum->x];(* (z+x)x ... \[Rule] zx + x^2 ... *)

If[!FreeQ[tmp,Pair[Momentum[x,___],Momentum[__]]],
tmp=tmp//.Power[xx_,power_Integer?Positive]/;!FreeQ[xx,Momentum[x,___]]:>Apply[times,Table[xx,{i,power}]];
tmp=tmp//.Pair[Momentum[x,dim___],Momentum[l_,dim___]]^power_Integer?Positive/;ToString[l]!=ToString[x]:>Apply[times,Table[Pair[Momentum[x,dim],Momentum[l,dim]],{i,power}]];

tmp=tmp//.Pair[Momentum[l_,dim___],Momentum[x,dim___]]/;ToString[l]!=ToString[x]:>(li=LorentzIndex[$AL[Unique[]],dim];Pair[li,Momentum[l,dim]] Pair[li,Momentum[x,dim]]);
	tmp=tmp/.times->Times;
	
];(* uncontract scaler product related to x :  xz \[Rule] x^\[Mu] z_\[Mu]; (xz)^n \[Rule] x^\[Mu] z_\[Mu]  x^\[Nu] z_\[Nu]... *)
tmp
]



Qdp[expr_,p_,OptionsPattern[]]:=Block[{tmp,l,null,contract=OptionValue[Contract],less=OptionValue[lessdummy],simp=OptionValue[Simplify]},
tmp=Qdx[expr,p,Contract->OptionValue[Contract],dp->True,lessdummy->OptionValue[lessdummy],Simplify->OptionValue[Simplify]](*Contract\[Rule]contract,dp->True,lessdummy\[Rule]less,Simplify\[Rule]simp*)
]


QTR[expr_]:=Block[{tmp,tmp2,i,null0,dot,resu=0,scheme},
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
tmp2=tmp2//.a___.DiracGamma[5].b_ .c___ :> If[FreeQ[b,DiracGamma], a.b.DiracGamma[5].c ,
			If[ToString[b]=="DiracGamma[5]",a.c,  -1 a.b.DiracGamma[5].c ]];
tmp2=tmp2/.Dot[z_]:>TR[Dot[z]];
resu=resu+tmp2

];
];

FCSetDiracGammaScheme[scheme];
resu/.null0->0
]



QExpand[expr_]:=Block[{tmp},

tmp=ExpandAll[expr//FCI];

tmp=tmp//.a___.(b_+c_).d___:>a.b.d+a.c.d;
tmp=tmp//.a___.(-1b_).d___:> -a.b.d;
tmp=tmp//.a___.(Pair[Momentum[b__],Momentum[b__]] c_).d___:>Pair[Momentum[b],Momentum[b]]a.c.d;
tmp=tmp//.a___.(Power[Pair[Momentum[b__],Momentum[b__]],e_] c_).d___:>Power[Pair[Momentum[b],Momentum[b]],e]a.c.d;

DiracGammaExpand[tmp]

]



QExpand[expr_,vec___]:=Block[{tmp},

tmp=ExpandAll[expr//FCI];

tmp=tmp//.a___.(b_+c_).d___:>a.b.d+a.c.d;
tmp=tmp//.a___.(-1b_).d___:> -a.b.d;
tmp=tmp//.a___.(Pair[Momentum[b__],Momentum[b__]] c_).d___:>Pair[Momentum[b],Momentum[b]]a.c.d;
tmp=tmp//.a___.(Power[Pair[Momentum[b__],Momentum[b__]],e_] c_).d___:>Power[Pair[Momentum[b],Momentum[b]],e]a.c.d;


tmp=Uncontract[DiracGammaExpand[tmp],vec];
(* expand  lorentz contarction related to vec :  \[Epsilon]^\[Mu]\[Nu]xz \[Rule] \[Epsilon]^\[Mu]\[Nu]\[Alpha]z x_\[Alpha]  ;  \[Gamma](x+z) \[Rule] \[Gamma]x +\[Gamma]z , \[Gamma]x \[Rule] \[Gamma]^\[Mu] x_\[Mu]] *)
If[!FreeQ[tmp,Times[_DiracGamma,Pair[Momentum[vec|vec+__|__-vec,___],LorentzIndex[__]]]],
	tmp=tmp//.{h___.Plus[others__,Times[g_DiracGamma,vector_]].l___:>h.Plus[others].l+h.g.l vector
	,h___.Times[g_DiracGamma,vector_].l___:>h.g.l vector};
];(* separate  \[Gamma].(\[Gamma]^\[Mu] x_\[Mu] + \[Gamma]z + \[Gamma] )...  ->  x_\[Mu] \[Gamma].\[Gamma]^\[Mu] ...   +   \[Gamma].(\[Gamma]z + \[Gamma])... *)

tmp
]






QAverage[expr_,p_]:=Block[{tmp,tmp2,tmp0,ap,list,null,null2,null0,l0,l1,i,j,l,n,k,m,tmpg,tmplist,times,plus},
tmp=expr//FCI;
tmp=tmp/.Momentum[xx_,dim___]/;!FreeQ[xx,p]:>Momentum[Expand[xx],dim];

tmp=tmp//.{Pair[Momentum[p+y_,dim___],LorentzIndex[index_,dim___]]:>Pair[Momentum[p,dim],LorentzIndex[index,dim]]+ Pair[Momentum[y,dim],LorentzIndex[index,dim]],
			Pair[Momentum[x_ p+y_,dim___],LorentzIndex[index_,dim___]]:>x Pair[Momentum[p,dim],LorentzIndex[index,dim]]+ Pair[Momentum[y,dim],LorentzIndex[index,dim]]};

If[!FreeQ[tmp,Momentum[p,___]],

If[!FreeQ[tmp,DiracGamma]||!FreeQ[tmp,Eps],tmp=Uncontract[DiracGammaExpand[tmp],p]];
(* uncontract if GSD[p] involved *)

tmp=tmp//.Pair[Momentum[p,___],LorentzIndex[index_,___]]:>null null2[index];

tmp=tmp null^2;(* seprate terms no FVD[p,mu] involved *)
tmp0=Collect[tmp,null]/.Power[null,a_]/;a>2 ->0;
tmp=tmp-tmp0;

tmp=Collect[null^2 tmp,null2[_]]/.Power[null,n_?OddQ]->0;


tmp=((tmp+null0 null2[l0]null2[l1])//Expand)/.Plus->plus;
tmp=tmp/.Power[null2[x_],m_]:>Apply[times,Table[null2[x],{k,m}]];

For[i=1,i<Length[tmp]+1,i++,
list={};
tmp2=tmp[[i]];
tmp2//.null2[a_]:>(list=Append[list,a];1);
m=Length[list]/2;

list=list//.List[l1_,ll___]:>(l=1;tmpg=0;tmplist=List[ll];
	n=Length[tmplist]+1;

	For[l=1,l<Length[tmplist]+1,l++,
	tmpg=tmpg+times[MTD[l1,tmplist[[1]]],tmplist[[2;;]]];
	tmplist=RotateLeft[tmplist]];
	tmpg);

tmp[[i]]=tmp[[i]] SPD[p]^m Product[1/(D+2k),{k,0,m-1}] list/.{}->1

];	

tmp=tmp0 + tmp/.{times->Times,plus->Plus,null2[_]->1,null->1,null0->0}
];

tmp

]



QAverage[expr_,p_,vectors_List]:=Block[{tmp,m,vector},
tmp=QAverage[expr,p]/.Momentum[xx_,dim___]:>Momentum[Expand[xx],dim];

For[m=1,m<Length[vectors]+1,m++,
	vector=vectors[[m]];
	tmp=tmp//.{Pair[Momentum[vector a_+y_,dd_],LorentzIndex[i_,dd_]]:> a Pair[Momentum[vector,dd],LorentzIndex[i,dd]]+Pair[Momentum[y,dd],LorentzIndex[i,dd]],
			Pair[Momentum[vector +y_,dd_],LorentzIndex[i_,dd_]]:> Pair[Momentum[vector,dd],LorentzIndex[i,dd]]+Pair[Momentum[y,dd],LorentzIndex[i,dd]],
			Pair[Momentum[vector a_,dd_],LorentzIndex[i_,dd_]]:> a Pair[Momentum[vector,dd],LorentzIndex[i,dd]]}];
	
tmp
]



AgammaD[expr___,OptionsPattern[]]:=Block[
{list,tmp,map,sign,resu,dim=OptionValue[Dimension]},
tmp=Level[{expr},{-1}];

list=Table[i,{i,1,Length[tmp]}];
map=Thread[Rule[list,tmp]];

tmp=Permutations[list];
sign=Signature[#]&/@tmp;

If[ToString[dim]=="4",
	1/Length[tmp]Total[sign(GA@@@(tmp/.map))],
	1/Length[tmp]Total[sign(GAD@@@(tmp/.map))]
	]
	
]

Agamma[expr___]:=AgammaD[expr,Dimension->4]



IndexSimplify[expr_,OptionsPattern[]]:=Block[
{tmp,tmp2,tmp3,cycl,dup,result=0,null,null0,a,b,plus,dot,i,j,k},

tmp=null (expr+null0 GAD[a,b])//Expand//FCI;
tmp=Replace[tmp,Plus->plus,{1},Heads->True];
tmp=tmp/.Dot->dot;
tmp2=tmp/.a___ dot[b___]:>dot[b];


tmp2=tmp2/.{DiracGamma[LorentzIndex[a_,___],___]:>a,DiracGamma[5]->-1};

If[OptionValue[Cyclic]===True,

	tmp2=tmp2/.dot[a___]:>(cycl={{a}};
		For[k=1,k<Length[{a}],k++,
		cycl=Append[cycl,RotateLeft[cycl[[-1]] ]] ];
		dummy[#]&/@cycl);
	
	
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

EndPackage[]
