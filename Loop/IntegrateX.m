(* ::Package:: *)

(* Wolfram Language package *)

(* Author: ShungHong Li *)





IntegrateX::usage = 
	"IntegrateX[expr,x] is a simple feyman integral in coordinate space for two feynman parameters"
	
	
	
Begin["`Private`IntegrateX`"]


Options[IntegrateX] = {
	Contract->False,
	dp->False,
	lessdummy->True,
	Simplify->True,
	ShowSteps->False}





IntegrateX[expr_,x_List/;Length[x]>1,opts___Rule]:=IntegrateX[IntegrateX[expr,x[[1]],opts],x[[2;;]],opts]

IntegrateX[expr_,{x_},opts___Rule]:=IntegrateX[expr,x,opts]

IntegrateX[expr_,x_,y__/;FreeQ[{y},Rule],opts___Rule]:=IntegrateX[IntegrateX[expr,x,opts],y,opts]






(*-----------------------------------------------------------*)

IntegrateX[expr_,x_,OptionsPattern[]]:=Block[
{tmp,tmp2,tmp3,tmp4,result=0,list,listlor,tmplist,glist,g,tmpg,i=1,j=1,n=1,k=1,null0,null1,null2,null5,nullx,tempresult,nullpo,nullpo2,nulllo,nulllo2,nullindx,lorindx,Ilist,
li,times,plus,mdim,momentum,pair2,test,wrong,pair,tttmp,rulem11,rulem12,fact,idp=OptionValue[dp],tmpdim,tmpxx},


tmp=(expr//FCI)//Expand;

(*-------------------------- seprate commutate part and none-commutate part --------------------------*)
tmp=tmp//.a___ . (b_+c_) . d___:>a . b . d+a . c . d;
tmp=tmp//.a___ . (-1b_) . d___:> -a . b . d;
tmp=tmp//.a___ . (Pair[Momentum[b_,dim___],Momentum[b_,dim___]] c_) . d___:>Pair[Momentum[b,dim],Momentum[b,dim]]a . c . d;
tmp=tmp//.a___ . (Power[Pair[Momentum[b_,dim___],Momentum[b_,dim___]],e_] c_) . d___:>Power[Pair[Momentum[b,dim],Momentum[b,dim]],e]a . c . d;
tmp=tmp//.a___ . (b_+c_) . d___:>a . b . d+a . c . d;
tmp=tmp//.a___ . (-1b_) . d___:> -a . b . d;



(* ------------------------------------------------------ unify the input ---------------------------------------------------------------------*)
(*(*  check the dimension *)
If[!FreeQ[tmp,(Momentum[xx_]/;!FreeQ[xx,x])|(Momentum[xx_,D-4]/;!FreeQ[xx,x])],
	If[!FreeQ[tmp,Momentum[x,D]|Momentum[x+_,D]|Momentum[_-x,D]],
		Print["Dimensional of ",x," inconsistent!"]];
	Print["All 4-dimensional ",x," will be treat as D-dimensional!"]];
*)
(* massless check *)
If[!FreeQ[tmp,PropagatorDenominator[Momentum[x|x+__|__ -x,___],mass_/;ToString[mass]!="0"]],
	Print["mass involved!"];Abort[]];


If[!FreeQ[tmp,FeynAmpDenominator],
	tmp=FeynAmpDenominatorSplit[tmp]/.{FeynAmpDenominator[PropagatorDenominator[xx_,mass___]]/;!FreeQ[xx,x]:>(
								tmpxx=(xx/.Momentum[pp_,dim___]:>(tmpdim=dim;pp));1/Pair[Momentum[tmpxx,tmpdim],Momentum[tmpxx,tmpdim]])}
];(* FAD[x] \[Rule] 1/SPD[x] *)


(*

If[!FreeQ[tmp,FeynAmpDenominator],
	tmp=FeynAmpDenominatorSplit[tmp]/.{FeynAmpDenominator[PropagatorDenominator[Momentum[xx_,dim___],mass_]]/;!FreeQ[xx,x]:>
			1/Pair[Momentum[xx,dim],Momentum[xx,dim]],
			FeynAmpDenominator[PropagatorDenominator[aa_ Momentum[xx_,dim___],mass_]]/;!FreeQ[xx,x]:>
			1/(aa^2 Pair[Momentum[xx,dim],Momentum[xx,dim]]),
		FeynAmpDenominator[PropagatorDenominator[Momentum[x,dim___] + Momentum[z_,dim___],mass_]]:>
			1/Pair[Momentum[x+ z,dim],Momentum[ x+ z,dim]],
		FeynAmpDenominator[PropagatorDenominator[aa_ Momentum[x,dim___] + Momentum[z_,dim___],mass_]]:>
			1/Pair[Momentum[aa x+ z,dim],Momentum[aa x+ z,dim]],
		FeynAmpDenominator[PropagatorDenominator[Momentum[x,dim___] + bb_ Momentum[z_,dim___],mass_]]:>
			1/Pair[Momentum[x+bb z,dim],Momentum[x+bb z,dim]],
		FeynAmpDenominator[PropagatorDenominator[aa_ Momentum[x,dim___] + bb_ Momentum[z_,dim___],mass_]]:>
			1/Pair[Momentum[aa x+bb z,dim],Momentum[aa x+bb z,dim]]}
];(* FAD[x] \[Rule] 1/SPD[x] *)
*)


(*------ Contract x_mu x^mu ------*)
tmp2=Cases[tmp,Pair[Momentum[xx_,___],LorentzIndex[llo_,___]]/;!FreeQ[xx,x]:>llo,Infinity];
If[Length[tmp2]>Length[DeleteDuplicates[tmp2]],tmp=QContract[tmp]];


(* if involve 2-loop *)
tmp=tmp/.Tarcer`TFI->QTFI;	

If[FreeQ[tmp,Pair[Momentum[xx_,___],Momentum[xx_,___]]/;!FreeQ[xx,x]]&&(tmp=!=0),
	Print["Check the input! "];Abort[]];
	


				
(*  -------- (x^2+2xy+y^2)->(x+y)^2 ----------  *)

If[!FreeQ[tmp,Power[aa_,nn_Negative]/;((Head[aa]===Plus)&&!FreeQ[aa,Pair])],
	tmp=tmp/.Power[aa_,nn_Negative]/;(Head[aa]===Plus):>Power[Factor[aa],nn]
];(*  1/(a x^2 + 2a xy +a y^2) \[Rule] 1/(a(x+y)^2) *)



tmp=tmp/.Power[aa_Plus,nn_]/;!FreeQ[aa,Momentum[___]]:>Power[aa/.Pair[Momentum[a_,dim___],Momentum[b_,dim___]]:>pair2[a,dim]pair2[b,dim],nn];
tmp=tmp/.Power[aa_,nn_]/;!FreeQ[aa,pair2[___]]:>Power[Factor[aa]/.bb1_ pair2[bb_,dim___]:>pair2[bb1 bb,dim],nn];
tmp=(tmp//.pair2[aa_,dim___]+pair2[bb_,dim___]:>pair2[aa+bb,dim])/.pair2[aa_,dim___]:>Pair[Momentum[aa,dim],Momentum[aa,dim]]^(1/2);
(*-----------------------------*)

tmp=tmp/.Pair[Momentum[z_+aa_ x,dim___],Momentum[z_+aa_ x,dim___]]:>aa^2 Pair[Momentum[x+z/aa,dim],Momentum[x+z/aa,dim]];
(*/.Pair[Momentum[z_-x,dim___],Momentum[z_-x,dim___]]:>Pair[Momentum[x-z,dim],Momentum[x-z,dim]]*)


(* ------------ ((c x^2)^n) \[Rule] c^n ((x^2)^n) ----------------- *)
tmp=tmp/.{Power[factor__ Pair[Momentum[x+z__,dim___],Momentum[x+z__,dim___]],power__]:>
			If[FreeQ[factor,-1],factor^power,(-1)^power(-factor)^power] Pair[Momentum[x+z,dim],Momentum[x+z,dim]]^power,	
			Power[factor__ Pair[Momentum[x,dim___],Momentum[x,dim___]],power__]:>
			If[FreeQ[factor,-1],factor^power,(-1)^power(-factor)^power]  Pair[Momentum[x,dim],Momentum[x,dim]]^power};

(* avoid mathematica take (-1)^(-1/2 D) as i^D; simplify (-1)^n since there are many term only differ by a sign*)
	
tmp=tmp/.{Power[factor__ Pair[Momentum[x+z__,dim___],Momentum[x+z__,dim___]],power__]:>
			(tmp3=Expand[power]/.D->0/.bb_+aa_/;NumberQ[aa]:>bb;
			tmp3=Boole[!NumberQ[tmp3]]tmp3;(* collect symbols neither numerical nor involve D *)
			tmp4=power-tmp3;
			If[FreeQ[factor,-1,1],factor^power,(-1)^tmp3(-1)^Quotient[4(tmp4/.D->0),4]I^(Quotient[Mod[4(tmp4/.D->0),4],2])(-1)^Expand[tmp4-(tmp4/.D->0)+Mod[Mod[4(tmp4)/.D->0,4],2]/4](-factor)^power]
			 Pair[Momentum[x+z,dim],Momentum[x+z,dim]]^power)
			,	
			Power[factor__ Pair[Momentum[x,dim___],Momentum[x,dim___]],power__]:>
			(tmp3=Expand[power]/.D->0/.bb_+aa_/;NumberQ[aa]:>bb;
			tmp3=Boole[!NumberQ[tmp3]]tmp3;(* collect symbols neither numerical nor involve D *)
			tmp4=power-tmp3;
			If[FreeQ[factor,-1,1],factor^power,(-1)^tmp3(-1)^Quotient[4(tmp4/.D->0),4]I^(Quotient[Mod[4(tmp4/.D->0),4],2])(-1)^Expand[tmp4-(tmp4/.D->0)+Mod[Mod[4(tmp4)/.D->0,4],2]/4](-factor)^power] 
			 Pair[Momentum[x,dim],Momentum[x,dim]]^power)};



	
If[!FreeQ[tmp,Pair[Momentum[x,dim___],Momentum[l_,dim___]]^power_Integer?Negative /;ToString[l]!=ToString[x]],
	Print[" 1/(",x,"z)^n type of input involved, current version can't deal with this!"];
	Abort[]];

(*-----------------------------------------------------------------------------------------------------------------------------------------------------------------------*)


tmp=QExpand[tmp,x,lessdummy->OptionValue[lessdummy]];
(* ------------------- gather the terms have same lorentz structure ----------------------- *)
If[(Head[tmp]===Plus)&&OptionValue[Simplify],
	(*tmp=tmp/.{nullIdentity->Identity};*)
	tmp=QSimplify2[tmp]
	
];

(*--------------------------------------------------------------- prepare for integrate ----------------------------------------------------------------------------------*)
(* ------------get denominator --------------*)
tmp=tmp nulllo[{nullindx}]+null0+null0^2//Expand;

tmp=(# nullpo[Cases[#,Pair[Momentum[xx_,D],Momentum[xx_,D]]^p_Integer?Negative /;!FreeQ[xx,x]:>{xx-x,-p},Infinity]])&/@tmp;
tmp=(# nullpo[Cases[#,Pair[Momentum[xx_,D],Momentum[xx_,D]]^p_/;(!FreeQ[xx,x])&&(!FreeQ[p,D]):>{xx-x,-p},Infinity]])&/@tmp;


tmp=tmp/.{Pair[Momentum[xx_,D],Momentum[xx_,D]]^p_Integer?Negative /;!FreeQ[xx,x]->1,Pair[Momentum[xx_,D],Momentum[xx_,D]]^p_/;(!FreeQ[xx,x])&&(!FreeQ[p,D])->1};

tmp=(# nullpo2[Cases[#,nullpo[{aa___}]:>aa,Infinity]])&/@tmp;

If[!FreeQ[tmp,nullpo2[aa_]/;Length[aa]>2],Print["Sorry! the current version can't deal with this!"];Abort[]];
tmp=tmp/.nullpo2[aa_]/;Length[aa]==1 -> 0;
tmp=tmp/.nullpo[___]->1;

(*---------- get numerators ------------*)

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

tmp=If[Head[tmp]=!=Plus,{tmp},List@@tmp];
	
If[OptionValue[Simplify],tmp=Replace[#,Plus[a_+b_]:>Simplify[a+b],{2}]&/@tmp ];


(* -------- sort the lorentz structure ------*)
(*tmp=tmp/.{nulllo2[cc__]:>nulllo2[cc//.{dd___,{aa1_,bb1_},{aa2_,bb2_},gg___}/;((ToString[aa1]!=ToString[aa2])&&(!FreeQ[{dd},{aa2,___}])):>{dd,{aa2,bb2},{aa1,bb1},gg}]};*)
tmp=tmp/.nulllo2[cc__]:>nulllo2[SortBy[cc,First]];
		
lorindx=tmp/.nullpo2[aa_]nulllo2[cc_]other___:>{aa,Transpose[cc]};
tmp=tmp/.{nullpo2[___]->1,nulllo2[___]->1};


(*---------------------------------------------------------------integrate---------------------------------------------------------------------------*)


Ilist=DeleteDuplicates[Replace[lorindx,{aa_,{bb_,ind_}}:>{aa,bb},{1}]];

Ilist=Replace[Ilist,{aa_,bb_}:>{aa,bb,getintegral[aa,bb,x,idp]},{1}];

lorindx=Cases[Ilist,{#[[1]],#[[2,1]],resu_}:>(resu[[1]]/.Thread[Rule[resu[[2]],#[[2,2]] ]])][[1]]&/@lorindx;

result=tmp lorindx//Total;

(*------------------------------------------------------------- do some simplification  ----------------------------------------------------------------------*)


(* --------------gather the terms have same lorentz structure -------------------*)
If[OptionValue[Simplify],

	result=Expand[result]//QContract;
	(*result=Contract[result/.qfact1[___]->0]+Replace[result,Except[aa_ qfact1[bb_]|qfact1[bb_]]->0,{1}]/.aa_ qfact1[bb_]:>Contract[aa]qfact1[bb]//Expand;*)
	
	If[Head[result]===Plus,
	
		result=QSimplify2[result,{Power[xx_,po_]/;!FreeQ[xx,Pair[___]]->1,Pair[___]->1,DiracGamma[___]->1,Eps[___]->1,DiracSigma[___]->1}]
	];
];



result=result/.{null1->0,null2->1,fact->Identity};


result=If[Length[null0+result/.{qGamma[1]->1,qGamma[2]->1,qGamma[3]->2}]==Length[result+null0],result/.{qGamma[1]->1,qGamma[2]->1,qGamma[3]->2},result];
(* if no potential problem, simplify small Gamma[n] *)

	If[ToLowerCase[ToString[OptionValue[Contract]]]=="true",
		result//Contract,
		result
		]
,
	0]

]




(*-----------------------------------------------------------*)



getintegral[list_,nn_,x_,dp_]:=Block[{result=0,tmp,tmp3,tmp4,tmp5,tmpg,listlor,tmplist,lln=Length[nn],x1,x2,i=1,j=1,k=1,n=1,l=1,nnl,times,
p1,p2,pp1,pp2,listlo,loo,null0,lloo,numerator,fpower,tmp6,tmp7,fmomentum,s1,s2,nx,momentum,co1,rule1},

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

(* -------------------- shift x ; simplify: 1 - s1 \[Rule] s2; 1 - s2 \[Rule] s1 ---------------------- *)
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


(* -------------------------- integrate term by term  -------------------------- *)
If[numerator=!={0},

	For[j=1,j<Length[numerator]+1,j++,

		tmp3=numerator[[j]];

		p1=Exponent[tmp3,s1];
		p2=Exponent[tmp3,s2];
		n=(Exponent[tmp3,nx]-1)/2;

		tmp3=Expand[tmp3]/.{nx->1,s1->1,s2->1};
		tmp3=tmp3+null0;


(* ------- generate normalized symmetry tensor g[\[Mu],\[Nu],\[Rho],\[Sigma],...] ----- *)

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
						tmpg=tmpg + times[Pair[LorentzIndex[l1,D],LorentzIndex[tmplist[[1]],D]],tmplist[[2;;]]];
						tmplist=RotateLeft[tmplist]];
						tmpg);
	(* times normalization factor qGamma[D/2]/(2^n qGamma[D/2 +n]) later *)
			listlor=(listlor/.{}->1)/.times->Times;

			tmp5=tmp5+tmp4 listlor qGamma[D/2]/(2^nnl qGamma[D/2 +nnl]);(* factor from average *)
			listlor={};
		];


(*---------------------------------------------- final result ----------------------------------------------*)

(*------ coefficients comes from x^0  \[Rule] -i x^0( p^0 \[Rule] i p^0 ), and integrate over x -----*)

		If[dp,
			pp1=fpower-n;(* since (z^2)^n/(z^2+x^2)^(fpower)>>>(-1)^(fpower-n) (-z^2)^(n)/(-z^2-x^2)^(fpower)  >>>wick rotation)>>> (-1)^(fpower-n) |z^2|^(n)/(|z^2|-x^2)^(fpower) *)
			pp2=-fpower+n+D/2;
			
			tmp6=Expand[pp1+pp2]/.D->0/.bb_+aa_/;NumberQ[aa]:>bb;
			tmp6=Boole[!NumberQ[tmp6]]tmp6;(* collect symbols neither numerical nor involve D *)
			tmp7=pp1+pp2-tmp6;
			
			co1=(-1)^tmp6(-1)^Quotient[4(tmp7+1/2/.D->0),4]I^(Quotient[Mod[4(tmp7+1/2/.D->0),4],2])(-1)^Expand[tmp7-(tmp7/.D->0)+Mod[Mod[4(tmp7+1/2)/.D->0,4],2]/4](1/(2Pi)^D);
		,
			pp1= 1+fpower-n;
			pp2= -fpower+n+D/2;
			
			tmp6=Expand[pp1+pp2]/.D->0/.bb_+aa_/;NumberQ[aa]:>bb;
			tmp6=Boole[!NumberQ[tmp6]]tmp6;(* collect symbols neither numerical nor involve D *)
			tmp7=pp1+pp2-tmp6;
			
			co1=(-1)^tmp6(-1)^Quotient[4(tmp7+1/2/.D->0),4]I^(Quotient[Mod[4(tmp7+1/2/.D->0),4],2])(-1)^Expand[tmp7-(tmp7/.D->0)+Mod[Mod[4(tmp7+tmp7+1/2)/.D->0,4],2]/4];
		];

		tmp5=tmp5  co1 Pi^(D/2)  qGamma[fpower-n-D/2]qGamma[n+D/2]/(qGamma[fpower]qGamma[D/2])Pair[Momentum[fmomentum,D],Momentum[fmomentum,D]]^pp2 ;


(* -----coefficients comes from feynman paramaterization, and integrate over parameter -----*)
		tmp5=tmp5 qGamma[fpower]/(qGamma[list[[1,2]]]qGamma[list[[2,2]]]) qGamma[n+p1+D/2 -list[[2,2]] ]qGamma[n+p2+D/2 -list[[1,2]] ]/qGamma[2n+p1+p2+D-fpower];

		result=result+(tmp5/.{null0->0})
	];
];


result = { result/.{null0->0},listlo}
];




(*-----------------------------------------------------------*)



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










End[]
