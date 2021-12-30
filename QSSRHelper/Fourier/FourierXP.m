(* Wolfram Language package *)



FourierXP::usage = 
"FourierXP[expr,{x,p}] is D-dimensional Fourier Transformation from
coordinate space {x} to momentum space {p}";

Begin["`Private`FourierXP`"]


Options[FourierXP]={
	TrueGamma->Integer,
	Dimension->"AsIs",
	Inverse->False,
	Simplify->True,
	Parallelize->"Auto"};
	
	
	
(* The basic logic is expand expr to several terms so that it have form:
                     ...(x^\[Nu])(x^\[Mu])((1/x^2)^n)+ ...(1/X^2)^m+...
then do fourier transformation term by term *)
 (*---------------------------------------------------------------------*)

FourierXP[expr_,{x_,pp_},OptionsPattern[]]:=Block[
{tmp,tmp2,test,rule1,dindex,findex,f,fco,result=0,tempresult,opt=OptionValue[TrueGamma],
inverse=OptionValue[Inverse],sign=-1,null2,null4,null5,nulllo,nullpo,nullindx,Flist={},lorindx={},times,li,wrong,i,j,k,p,parall=OptionValue[Parallelize]},

tmp=expr//FCI;

If[FreeQ[tmp,Pair[Momentum[x,___],Momentum[x,___]]|FeynAmpDenominator[PropagatorDenominator[Momentum[x,___],___]]]||(!FreeQ[tmp,pp]),
	Print["No ",ToString[x]," involved in input!"];
	tmp
,
	
	
(*---------------------------------deal with input--------------------------------*)
	If[!FreeQ[tmp,FeynAmpDenominator],
		tmp=FeynAmpDenominatorSplit[tmp]/.FeynAmpDenominator[PropagatorDenominator[Momentum[x,dim___],mass_]]:>
		(If[mass!=0,Print["mass in denorminator will be ignore!"]];1/Pair[Momentum[x,dim],Momentum[x,dim]])
	];(* FAD[x] \[Rule] 1/SPD[x] *)


	tmp=tmp/.Power[aa_,nn_]:>Power[Collect[aa,Pair[___]],nn];(* 1/(a x^2 + b x^2) \[Rule] 1/((a+b)x^2) *)
	
	
(* stop when 1/(xz)^n involved *)
	test=tmp/.Pair[Momentum[x,dim___],Momentum[l_,dim___]]^power_Integer?Negative/;ToString[l]!=ToString[x]:>(Print[Pair[Momentum[x,dim],Momentum[l,dim]]^power," involved!"];Abort[]);


(*-----------------------------------Expand numerator; get the vector ------------------------------------------*)
	tmp=QExpand[QSimplify2[tmp],x,lessdummy->True];

	tmp=tmp/.{Pair[Momentum[zz_+x,dim___],LorentzIndex[lor_,dim___]]:>Pair[Momentum[zz,dim],LorentzIndex[lor,dim]]+ Pair[Momentum[x,dim],LorentzIndex[lor,dim]],
				Pair[Momentum[zz_+aa_ x,dim___],LorentzIndex[lor_,dim___]]:>Pair[Momentum[zz,dim],LorentzIndex[lor,dim]]+ aa Pair[Momentum[x,dim],LorentzIndex[lor,dim]]};
				
(* ------------ ((c x^2)^n) \[Rule] c^n ((x^2)^n) ----------------- *)
	tmp=tmp/.{Power[factor__ Pair[Momentum[x,dim___],Momentum[x,dim___]],power__]:>
				If[FreeQ[factor,-1],factor^power,(-1)^power(-factor)^power] Pair[Momentum[x,dim],Momentum[x,dim]]^power,	
				Power[factor__ Pair[Momentum[aa_ x,dim___],Momentum[aa_ x,dim___]],power__]:>
				If[FreeQ[factor,-1],factor^power,(-1)^power(-factor)^power] (aa^2)^power Pair[Momentum[x,dim],Momentum[x,dim]]^power};


(* --------------------- (x+y)^u \[Rule] x^u + y^u -------------------------- *)
	tmp=Expand[tmp/.Pair[Momentum[xx_,dim___],LorentzIndex[lor_,dim___]]/;!FreeQ[xx,x]:>Pair[Momentum[xx-(xx/.x->0),dim],LorentzIndex[lor,dim]]+Pair[Momentum[(xx/.x->0),dim],LorentzIndex[lor,dim]] ];
	
(*------ Contract x_u x^u ------*)
	tmp2=Cases[tmp,Pair[Momentum[x,D],LorentzIndex[llo_,D]]:>llo,Infinity];
	If[Length[tmp2]>Length[DeleteDuplicates[tmp2]],
		tmp=Collect[tmp,Pair[Momentum[x,D],LorentzIndex[_,D]]];
		tmp=tmp/.Power[Pair[Momentum[x,D],LorentzIndex[lor_,D]],2]:>Pair[Momentum[x,D],Momentum[x,D]]
	];


(*-----------------------------------------------------*)

	tmp = null2 nulllo[nullindx] tmp Pair[Momentum[x,D],Momentum[x,D]]^null5;(* to avoid discuss the form of tmp *)
	tmp = Expand[tmp,Pair[Momentum[x,___],_]]/.Power[factor_ Pair[Momentum[x,D],Momentum[x,D]],power_]:>factor^power Pair[Momentum[x,D],Momentum[x,D]]^power;


(*-------------- gather the terms have same lorentz structure;  Simplify Gamma functions -----------------*)
	If[(Head[tmp]===Plus)&&OptionValue[Simplify],
		tmp=QSimplify2[tmp,{null2->1,nulllo[___]->1,nullpo[___]->1}]	
	];

(*-------------------------------*)
	tmp=tmp//Expand;
	
	If[tmp===0,
		0
	,
		If[Head[tmp]===Plus,
			tmp=List@@tmp;
	
			tmp=(nulllo@@Cases[#,Pair[Momentum[x,D],LorentzIndex[lor_,D]]:>lor,Infinity])(nullpo@@Cases[#,Power[Pair[Momentum[x,D],Momentum[x,D]],por_]:>por,Infinity])#&/@tmp;
	
			tmp=tmp/.{Pair[Momentum[x,D],LorentzIndex[lor_,D]]->1,Power[Pair[Momentum[x,D],Momentum[x,D]],por_]->1};
	
			tmp=Collect[tmp//Total,nulllo[___]]//Expand;
		,
			tmp=tmp(nulllo@@Cases[tmp,Pair[Momentum[x,D],LorentzIndex[lor_,D]]:>lor,Infinity])(nullpo@@Cases[tmp,Power[Pair[Momentum[x,D],Momentum[x,D]],por_]:>por,Infinity]);
			tmp=tmp/.{Pair[Momentum[x,D],LorentzIndex[lor_,D]]->1,Power[Pair[Momentum[x,D],Momentum[x,D]],por_]->1};
		];
	

		tmp=tmp/.nulllo[nullindx]nulllo[aa___]:>nulllo[nullindx,aa]/.nullpo[aa_]:>nullpo[aa/.null5:>0];
		tmp=tmp/.nullpo[aa_Integer]/;aa>=0 :>0;(* aa>= 0 get 0 since 1/Gamma[-aa](-aa\[LessEqual]0) = 0 *)
		tmp=tmp//Expand;
		
(*---------------------------------------------------- fourier transform term by term ----------------------------------------------*)
(*------------------ get lorentz structure, the term with same lorentz structure have same result only differ by lorentz indices -------------------*)

		tmp=If[Head[tmp]=!=Plus,{tmp},List@@Expand[tmp]];

		tmp=tmp/.nulllo[nullindx,aa___]:>nulllo[aa];
		lorindx=tmp/.nullpo[aa_]nulllo[bb___]___:>{aa,{bb}};
		(*lorindx=Replace[lorindx,{aa_Integer,bb_}/;aa>0 ->{0,0},{1}];*)
		
		Flist=DeleteDuplicates[Replace[lorindx,{bb___}:>Length[{bb}],{2}]];

		Flist=Replace[Flist,{aa_,bb_}:>{aa,bb,getfourier[aa,bb,x,p,inverse]},{1}];

		tmp=tmp/.nullpo[___]nulllo[___]other_:>other;

		lorindx=Cases[Flist,{#[[1]],Length[#[[2]]],resu_}:>(resu[[2]]/.Thread[Rule[resu[[1]],#[[2]] ]])][[1]]&/@lorindx;
		
		(*
		If[Length[lorindx]<40,
			lorindx=Cases[Flist,{#[[1]],Length[#[[2]]],resu_}\[RuleDelayed](resu[[2]]/.Thread[Rule[resu[[1]],#[[2]] ]])][[1]]&/@lorindx
		,
			Do[null5=Flist/.{lorindx[[i,1]],Length[lorindx[[i,2]]],c_}:>(tempresult=c;1);
						lorindx[[i]]=tempresult[[2]]/.Thread[Rule[tempresult[[1]],lorindx[[i,2]]]],{i,Length[lorindx]}]
		];
		*)
		
		result=lorindx tmp//Total;
(* -----------------------gather the terms have same lorentz structure after Fourier transform;  Simplify Gamma functions ------------------*)

		If[OptionValue[Simplify],
			result=Expand[result]//QContract;
		(*result=Contract[result/.qfact1[___]->0]+Replace[result,Except[aa_ qfact1[bb_]|qfact1[bb_]]->0,{1}]/.aa_ qfact1[bb_]:>Contract[aa]qfact1[bb]//Expand;*)
	
			If[Head[result]===Plus,
				result=QSimplify2[result,{null2->1,nulllo[___]->1,nullpo[___]->1}]
			];	
		];


		result=result/.{null2->1,p:>pp};


		If[opt==Integer, result=result/.qGamma[nn_Integer]/;nn<4 :>Gamma[nn]];

		If[opt==All,result=result/.qGamma:>qGamma2];

		result
	]
]

]




(*--------------------------------------------------------------------------*)

getfourier[d_,n_,x_,p_,inver_]:=Block[{findex=-d,dindex={},sign=-1,factor=1,fco,f,co1,co2,null3,tmp,ii,jj,res},

(*If[(d===0)&&(n===0),
	{0,0}
,*)
	If[inver==True,sign=1;factor=(2Pi)^(-D)];
	If[d==0,Print["terms with no ",SuperscriptBox[x,2]//DisplayForm," involved, please make sure the input is correct!"]];

	co2=(-1)^Quotient[4((-D/2+findex)/.D->0),4]I^(Quotient[Mod[4((-D/2+findex)/.D->0),4],2])(-1)^Expand[(-D/2+findex)-((-D/2+findex)/.D->0)+Mod[Mod[4((-D/2+findex))/.D->0 ,4],2]/4];
	co1=(-1)^Quotient[4((findex+1/2)/.D->0),4]I^(Quotient[Mod[4((findex+1/2)/.D->0),4],2])(-1)^Expand[(findex+1/2)-((findex+1/2)/.D->0)+Mod[Mod[4((findex+1/2))/.D->0 ,4],2]/4];

	fco=sign factor co1 2^(D-2findex) Pi^(D/2) qGamma[D/2 - findex]/qGamma[findex];
	f=co2 Pair[Momentum[p,D],Momentum[p,D]]^null3[-D/2+findex];
(* for findex<= 0 it get 0 because 1/Gamma[n](n\[LessEqual]0) = 0 *)

(* --------derivative if needed---------- *)

	If[n=!=0,
		dindex=Table[$AL[Unique[]],{ii,1,n}];

		For[jj=1, jj<n+1, jj++,
			f = sign I FourDivergence[f,Pair[Momentum[p,D],LorentzIndex[dindex[[jj]],D]]];
			f = f/.{Times[null3[xx_]+yy_,zz__]:> -zz qGamma[-xx-yy+1]/qGamma[-xx-yy],Times[null3[xx_],zz__]:> -zz qGamma[-xx +1]/qGamma[-xx]}
		]
	
(* derivative; simplify the factor generated by derivative to qGamma[]/qGamma[]. sometime, e.g. (D-4)qGamma[D-4] = qGamma[D-3], but if set D=4 first, it = 0 since qGamma[] is just a symbol *)
	];


	res={dindex,Simplify[fco*f]/.{null3->Identity}}(* simplify qGamma[], to avoid terms like ...qGamma[0].../(...qGamma[0]...), which may cause error *)

(*]*)
];
 
 
 
 (*---------------------------------------------------------------------*)
 

End[]
(*EndPackage[]*)