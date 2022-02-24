(* Wolfram Language package *)

(* Author: ShungHong Li *)




QExpand::usage = 
	"QExpand[expr_,p_] seprate commute and noncommute part, expand Lorentz sturcture involved with p."
	
Begin["`Private`QExpand`"]

Options[QExpand] = {
	lessdummy->True}
	
	
(*-------------------------------------------------*)	

QExpand[expr_,{x_,xx__},opts___Rule]:=QExpand[QExpand[expr,x,opts],{xx},opts]
QExpand[expr_,{x_},opts___Rule]:=QExpand[expr,x,opts]





(*-------------------------------------------------*)
QExpand[expr_,x_,OptionsPattern[]]:=Block[{tmp,tmp2,plus,times,dot,li,null,dum=OptionValue[lessdummy],dumlist,dumlist2,dumlist3={},nn,maxlength,i=1,l1,l2,lorindx,momentum,pair,tmpl,tmpl2,tmpl4,reprule,lorentzIndex},

tmp=(expr//FCI)/.Power[Plus[a_+b_],c_?Negative]:>Power[plus[a,b],c];
tmp=tmp/.{Plus[a_+D]:>plus[a+D],Plus[a_-D]:>plus[a-D]};
tmp=ExpandAll[tmp];


(*-------------------- extract commutate part from none-commutate \[Gamma] struct-----------------------------*)
tmp=tmp//.a___ . (b_+c_) . d___:>a . b . d+a . c . d;
tmp=tmp//.a___ . (-1b_) . d___:> -a . b . d;
tmp=tmp//.a___ . (Pair[Momentum[b_,dim___],Momentum[b_,dim___]] c_) . d___:>Pair[Momentum[b,dim],Momentum[b,dim]]a . c . d;
tmp=tmp//.a___ . (Power[Pair[Momentum[b_,dim___],Momentum[b_,dim___]],e_] c_) . d___:>Power[Pair[Momentum[b,dim],Momentum[b,dim]],e]a . c . d;
tmp=tmp//.a___ . (b_+c_) . d___:>a . b . d+a . c . d;
tmp=tmp//.a___ . (-1b_) . d___:> -a . b . d;

If[!FreeQ[ tmp/.Dot->dot , dot[a___]/;!FreeQ[{a} , Momentum[xx_,___]/;!FreeQ[xx,x] ] ],
	tmp=QExpand2[DiracGammaExpand[tmp/.plus->Plus]]
];


(*------------------- expand  x from dirac struct, epsilon tensor, \[Epsilon]^\[Mu]\[Nu]xz \[Rule] \[Epsilon]^\[Mu]\[Nu]\[Alpha]z x_\[Alpha] ,  \[Gamma](x+z) \[Rule] \[Gamma]^u (x+z)_u ------------------- *)
tmp=tmp/.Momentum[aa_,dim___]:>Momentum[aa/.Plus->plus,dim];
tmp=Uncontract[DiracGammaExpand[tmp],x];
tmp=tmp/.plus->Plus;



(* -------------------------uncontract scaler product, xz \[Rule] x^\[Mu] z_\[Mu]; (xz)^n \[Rule] times{x^u z_u , x^v z_v , ... } -----------------------*)
tmp=tmp/.Power[xx_,power_Integer?Positive]/;!FreeQ[xx,Momentum[xy_/;!FreeQ[xy,x],___]]:>Apply[times,Table[xx,{i,power}]];
(*tmp=tmp/.Pair[Momentum[x,dim___],Momentum[l_,dim___]]^power_Integer?Positive:>Apply[times,Table[Pair[Momentum[x,dim],Momentum[l,dim]],{i,power}]];*)

tmp=tmp/.Power[xx_,power_]/;!FreeQ[xx,Momentum[xy_/;!FreeQ[xy,x],___]]:>Power[xx/.Momentum->momentum,power];(* avoid expand xy in denominator like (x^2+2xy +y^2)^(D-n) *)
tmp=tmp/.Pair[Momentum[l_,dim___],Momentum[xx_,dim___]]/;!FreeQ[xx,x]:>(li=LorentzIndex[$AL[Unique[]],dim];Pair[li,Momentum[l,dim]] Pair[li,Momentum[xx,dim]]);
	
tmp=tmp/.{times->Times,momentum->Momentum,null->0};


(*------------------------------------------------------------------------------------------------------------------- *)
(* ------(p^u)^2 \[Rule] p^u g^uu' p^u' ; write 4-d or (D-4)-d vector as D-d vector times with 4-d or (4-D)-d metric -----*)

tmp=tmp/.{Power[Pair[Momentum[xx_/;!FreeQ[xx,x],D],LorentzIndex[lo_,D]],2]:>
							(li=$AL[Unique[]];Pair[Momentum[xx,D],LorentzIndex[li,D]]Pair[LorentzIndex[li,D],LorentzIndex[lo,D]]Pair[Momentum[xx,D],LorentzIndex[lo,D]]),
			Power[Pair[Momentum[xx_/;!FreeQ[xx,x],D-4],LorentzIndex[lo_,D-4]],2]:>
							(li=$AL[Unique[]];Pair[Momentum[xx,D],LorentzIndex[li,D]]Pair[LorentzIndex[li,D-4],LorentzIndex[lo,D-4]]Pair[Momentum[xx,D],LorentzIndex[lo,D]]),
			Power[Pair[Momentum[xx_/;!FreeQ[xx,x]],LorentzIndex[lo_]],2]:>
							(li=$AL[Unique[]];Pair[Momentum[xx,D],LorentzIndex[li,D]]Pair[LorentzIndex[li],LorentzIndex[lo]]Pair[Momentum[xx,D],LorentzIndex[lo,D]])};

tmp=tmp/.{Pair[Momentum[xx_],LorentzIndex[lo_]]/;!FreeQ[xx,x]:>(li=$AL[Unique[]];Pair[Momentum[xx,D],LorentzIndex[li,D]]Pair[LorentzIndex[li],LorentzIndex[lo]]),
			Pair[Momentum[xx_,D-4],LorentzIndex[lo_,D-4]]/;!FreeQ[xx,x]:>(li=$AL[Unique[]];Pair[Momentum[xx,D],LorentzIndex[li,D]]Pair[LorentzIndex[li,D-4],LorentzIndex[lo,D-4]])};

(*--------------------------------------------------------------------------------------------------------------------------*)
(* simplify dummy indices, since mathematica doesn't know x^u z_u = x^v z_v, which make the expresion very long sometime *)

tmp=tmp//Expand;
If[dum&&(Head[tmp]===Plus),
	tmp=List@@tmp;
	
	tmp=tmp/.Pair[Momentum[xx_,dim___],LorentzIndex[lo_,dim___]]/;!FreeQ[xx,x]:>pair[Momentum[xx,dim],lorentzIndex[lo,dim]];
	
	tmpl=Cases[#,pair[Momentum[xx_,dim___],lorentzIndex[lo_,dim___]]/;!FreeQ[#,LorentzIndex[lo,___]]:>lo,Infinity]&/@tmp;
	tmpl=DeleteDuplicates[#]&/@tmpl;
	tmp=tmp/.{pair->Pair,lorentzIndex->LorentzIndex};
	
	(* generate new lorentz indices, replace the existed dummy indices *)		
	tmpl4=Length[#]&/@tmpl;
	dumlist2=Table[$AL[Unique[]],Max[tmpl4]];
(*  must generate new dummy indices to avoid conflict with existed dummy indices, 
			e.g    A * Eps[a,b,c,d]Eps[a,b,e,f]x_c z_d + B * y^a x_a  y^b x_b , below may replace c\[Rule]a,d\[Rule]b if not generate new dummy indices  *)
	
	tmp=MapThread[#1/.Thread[Rule[#2,dumlist2[[ 1;; Length[#2] ]] ] ]&,{tmp,tmpl}];
		
	tmp=tmp//Total
];


tmp
]






(*-------------------------------------------------*)

End[]