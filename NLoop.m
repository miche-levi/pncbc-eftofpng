(* ::Package:: *)

(* ::Title:: *)
(*Package EFTofPNG version 0.99*)


(* ::Chapter:: *)
(*EFTofPNG: NLoop*)


(* ::Subchapter:: *)
(*Copyright*)


(* ::Text:: *)
(*Copyright (C) 2017  Michele Levi*)
(*Copyright (C) 2017  Jan Steinhoff*)
(**)
(*This file is part of EFTofPNG.*)
(**)
(*EFTofPNG is free software: you can redistribute it and/or modify*)
(*it under the terms of the GNU General Public License as published by*)
(*the Free Software Foundation, either version 3 of the License, or*)
(*(at your option) any later version.*)
(**)
(*EFTofPNG is distributed with the intention of being widely useful,*)
(*but WITHOUT ANY WARRANTY; without even the implied warranty of*)
(*MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the*)
(*GNU General Public License for more details.*)
(**)
(*You should have received a copy of the GNU General Public License*)
(*along with EFTofPNG.  If not, see <http://www.gnu.org/licenses/>.*)


(* ::Subchapter::Closed:: *)
(*Setup*)


(* ::Subsection::Closed:: *)
(*init xTensor *)


(*load xTensor package*)
Needs["xAct`xTensor`"]
$DefInfoQ=False;
$UndefInfoQ=False;


(*setup d-dimensional manifold and time parameter*)
DefConstantSymbol[d]
DefManifold[Md,d,{i,j,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,j1,j2,j3,j4,j5,j6,j7,j8,j9,j10,j11,j12,j13,j14,j15,j16,j17,j18,j19,l}]
(*k is reserved for the Fourier momenta*)
DefMetric[1,\[Delta][-i,-j],CD,{",","\[PartialD]"},FlatMetric->True]
DefParameter[t]
SetOptions[MakeRule,{MetricOn->All,ContractMetrics->True}];


(* ::Subsection::Closed:: *)
(*def constants*)


(*gravitational constant*)
DefConstantSymbol[G]


(*a manifold for constant tensors*)
DefManifold[Const,0,{}]
ConstTensorQ[T_?xTensorQ]:=MemberQ[DependenciesOfTensor[T],Const]
ConstTensorQ[_]=False;


(*masses*)
DefTensor[m[LI[]],Const]


(*spin-multipole Wilson coefficients*)
DefTensor[CES2[LI[]],Const]
DefTensor[CBS3[LI[]],Const]
DefTensor[CES4[LI[]],Const]


(* ::Subsection::Closed:: *)
(*def worldline DOFs*)


(*positions, position difference, and distance*)
DefTensor[x[LI[],LI[],i],{Md,t}]
DefTensor[xRel[LI[],LI[],i],{Md,t}]
DefTensor[r[LI[],LI[]],{Md,t}]
SetAttributes[r,Orderless]
DefTensor[n[LI[],LI[],i],{Md,t}]
xRel2n[ex_]:=ex/.{xRel[L__,i_]:>n[L,i]r[L]}
n2xRel[ex_]:=ex/.{n[L__,i_]:>xRel[L,i]/r[L]}


(*momenta*)
DefTensor[p[LI[],i],{Md,t}]
DefTensor[phat[LI[],i],{Md,t}]


(*spin tensor, vector, and length square*)
DefTensor[S[LI[],LI[],i,j],{Md,t},Antisymmetric[{i,j}]]
DefTensor[Sv[LI[],LI[],i],{Md,t}]
DefTensor[Ssq[LI[],LI[]],{Md,t},PrintAs->"\!\(\*SuperscriptBox[\(S\), \(2\)]\)"]


(*conversion between vector and tensor*)
toSpinV[ex_]:=ex/.S[A__,i_,j_]:>Module[{l},epsilon\[Delta][i,j,l]Sv[A,-l]]
toSpinT[ex_]:=ex/.Sv[A__,l_]:>Module[{i,j},epsilon\[Delta][l,i,j]/2S[A,-i,-j]]


(* ::Subsection::Closed:: *)
(*def labels*)


(*aux functions and heads for labels of tensors:
first label for a point, either worldline or bulk/field,
second label for order of time derivative*)


(*generic head for points*)
p[A_]:=LI@A
(*head for time derivative*)
td[A_]:=LI@DT@A
(*generic point & time derivative*)
pdt[A_,B_]:=Sequence[p@A,td@B]


(*head for worldline points*)
wl[A_]:=p@WL@A
wl[A_,B_]:=pdt[WL@A,B]


(*head for bulk/field points*)
pt[A_]:=p@PT@A
pt[A_,B_]:=pdt[PT@A,B]


(*handle time derivative label*)
incDt[x_[pdt[A_,n_],i___]]:=x[pdt[A,n+1],i]
decDt[x_[pdt[A_,n_],i___]]:=x[pdt[A,n-1],i]
addDt[n_][A_,td[B_],C___]:=Sequence[A,td[B+n],C]


(* ::Subsection::Closed:: *)
(*output labels*)


SetAttributes[interpretbox,HoldFirst]
interpretbox[expr_,box_]:=InterpretationBox[StyleBox[box,AutoSpacing->False],expr,Editable->False]


(*output lables of constants*)
MakeBoxes[m[LI[WL[w_]]],StandardForm]^:=interpretbox[m[LI[WL[w]]],SubscriptBox[MakeBoxes[m],MakeBoxes[w]]]
MakeBoxes[CES2[LI[WL[w_]]],StandardForm]^:=interpretbox[CES2[LI[WL[w]]],SubscriptBox[MakeBoxes[C],GridBox[{{MakeBoxes[ES^2],MakeBoxes[w]}},ColumnSpacings->0.05]]]
MakeBoxes[CBS3[LI[WL[w_]]],StandardForm]^:=interpretbox[CBS3[LI[WL[w]]],SubscriptBox[MakeBoxes[C],GridBox[{{MakeBoxes[BS^3],MakeBoxes[w]}},ColumnSpacings->0.05]]]
MakeBoxes[CES4[LI[WL[w_]]],StandardForm]^:=interpretbox[CES4[LI[WL[w]]],SubscriptBox[MakeBoxes[C],GridBox[{{MakeBoxes[ES^4],MakeBoxes[w]}},ColumnSpacings->0.05]]]


(*make all indices Euclidean*)
makeEuclid[-a_]:=a
makeEuclid[a_]:=a


(*output labels of x*)
MakeBoxes[x[LI[WL[w_]],LI[DT[0]],i_],StandardForm]^:=interpretbox[x[LI[WL[w]],LI[DT[0]],i],SubsuperscriptBox[MakeBoxes[x],MakeBoxes[w],First[MakeBoxes/@makeEuclid/@{i}]]]
MakeBoxes[x[LI[WL[w_]],LI[DT[1]],i_],StandardForm]^:=interpretbox[x[LI[WL[w]],LI[DT[1]],i],SubsuperscriptBox["v",MakeBoxes[w],First[MakeBoxes/@makeEuclid/@{i}]]]
MakeBoxes[x[LI[WL[w_]],LI[DT[2]],i_],StandardForm]^:=interpretbox[x[LI[WL[w]],LI[DT[2]],i],SubsuperscriptBox["a",MakeBoxes[w],First[MakeBoxes/@makeEuclid/@{i}]]]
MakeBoxes[x[LI[WL[w_]],LI[DT[n_]],i_],StandardForm]^:=Module[{nd},
Hold[interpretbox[x[LI[WL[w]],LI[DT[n]],i],SubsuperscriptBox[OverscriptBox[MakeBoxes[a],AdjustmentBox[GridBox[{{"(",MakeBoxes[nd],")"}},ColumnSpacings->-0.3],BoxMargins->{{-0.3,-0.3},{0,0}}]],MakeBoxes[w],AdjustmentBox[GridBox[{MakeBoxes/@makeEuclid/@{i}},ColumnSpacings->0.05],BoxBaselineShift->0.7]]]]/.nd->n-2//ReleaseHold]


(*output labels of r and n*)
MakeBoxes[xRel[LI[WL[w1_]],LI[WL[w2_]],i_],StandardForm]^:=interpretbox[xRel[LI[WL[w1]],LI[WL[w2]],i],SubsuperscriptBox[MakeBoxes[x],GridBox[{{MakeBoxes[w1],MakeBoxes[w2]}},ColumnSpacings->0.05],First[MakeBoxes/@makeEuclid/@{i}]]]
MakeBoxes[x[LI[WL[w1_]],LI[WL[w2_]],i_],StandardForm]^:=interpretbox[x[LI[WL[w1]],LI[WL[w2]],i],SubsuperscriptBox[MakeBoxes[x],GridBox[{{MakeBoxes[w1],MakeBoxes[w2]}},ColumnSpacings->0.05],First[MakeBoxes/@makeEuclid/@{i}]]]
MakeBoxes[r[LI[WL[w1_]],LI[WL[w2_]]],StandardForm]^:=interpretbox[r[LI[WL[w1]],LI[WL[w2]]],SubscriptBox[MakeBoxes[r],GridBox[{{MakeBoxes[w1],MakeBoxes[w2]}},ColumnSpacings->0.05]]]
MakeBoxes[n[LI[WL[w1_]],LI[WL[w2_]],i_],StandardForm]^:=interpretbox[n[LI[WL[w1]],LI[WL[w2]],i],SubsuperscriptBox[MakeBoxes[n],GridBox[{{MakeBoxes[w1],MakeBoxes[w2]}},ColumnSpacings->0.05],First[MakeBoxes/@makeEuclid/@{i}]]]


(*output labels of S*)
MakeBoxes[S[LI[WL[w_]],LI[DT[0]],i__],StandardForm]^:=interpretbox[S[LI[WL[w]],LI[DT[0]],i],SubsuperscriptBox[MakeBoxes[S],MakeBoxes[w],GridBox[{MakeBoxes/@makeEuclid/@{i}},ColumnSpacings->0.05]]]
MakeBoxes[S[LI[WL[w_]],LI[DT[n_]],i__],StandardForm]^:=interpretbox[S[LI[WL[w]],LI[DT[n]],i],SubsuperscriptBox[OverscriptBox[MakeBoxes[S],AdjustmentBox[GridBox[{{"(",MakeBoxes[n],")"}},ColumnSpacings->-0.3],BoxMargins->{{-0.3,-0.3},{0,0}}]],MakeBoxes[w],AdjustmentBox[GridBox[{MakeBoxes/@makeEuclid/@{i}},ColumnSpacings->0.05],BoxBaselineShift->0.7]]]
MakeBoxes[Sv[LI[WL[w_]],LI[DT[0]],i_],StandardForm]^:=interpretbox[Sv[LI[WL[w]],LI[DT[0]],i],SubsuperscriptBox[MakeBoxes[S],MakeBoxes[w],GridBox[{MakeBoxes/@makeEuclid/@{i}},ColumnSpacings->0.05]]]
MakeBoxes[Sv[LI[WL[w_]],LI[DT[n_]],i_],StandardForm]^:=interpretbox[Sv[LI[WL[w]],LI[DT[n]],i],SubsuperscriptBox[OverscriptBox[MakeBoxes[S],AdjustmentBox[GridBox[{{"(",MakeBoxes[n],")"}},ColumnSpacings->-0.3],BoxMargins->{{-0.3,-0.3},{0,0}}]],MakeBoxes[w],AdjustmentBox[GridBox[{MakeBoxes/@makeEuclid/@{i}},ColumnSpacings->0.05],BoxBaselineShift->0.7]]]
MakeBoxes[Ssq[LI[WL[w_]],LI[DT[0]]],StandardForm]^:=interpretbox[Ssq[LI[WL[w]],LI[DT[0]]],SubsuperscriptBox[MakeBoxes[S],MakeBoxes[w],AdjustmentBox[MakeBoxes[2],BoxBaselineShift->-0.5]]]
MakeBoxes[Ssq[LI[WL[w_]],LI[DT[n_?Positive]]],StandardForm]^:=interpretbox[Ssq[LI[WL[w]],LI[DT[n]]],SubsuperscriptBox[OverscriptBox[MakeBoxes[S],AdjustmentBox[GridBox[{{"(",MakeBoxes[n],")"}},ColumnSpacings->-0.3],BoxMargins->{{-0.3,-0.1},{0,0}}]],MakeBoxes[w],AdjustmentBox[MakeBoxes[2],BoxBaselineShift->-0.5]]]


(* ::Subsection::Closed:: *)
(*tools*)


(*simplification rules for m,x*)
mRule={m[A_]:>Scalar[m[A]]};
xRule={
x[wl[A_,0],i_]-x[wl[B_,0],i_]:>(xRel[wl[A],wl[B],i]/.xRule),
xRel[A_,B_,i_]:>Order[A,B]xRel[Sequence@@Sort[{A,B}],i],
xRel[A_,B_,i_]xRel[A_,B_,-i_]:>Scalar[r[A,B]]^2,
xRel[A_,B_,i_]xRel[B_,A_,-i_]:>-Scalar[r[A,B]]^2,
r[A__]:>Scalar[r[A]],
(r[A__]^n1_)^n2_:>Scalar[r[A]]^(n1 n2),
(Scalar[r[A__]]^n1_)^n2_:>Scalar[r[A]]^(n1 n2),
Log[r[A__]^n_]:>n Log@Scalar@r[A],
Log[Scalar[r[A__]]^n_]:>n Log@Scalar@r[A],
n[A_,B_,i_]:>Order[A,B]n[Sequence@@Sort[{A,B}],i],
n[A_,B_,i_]n[A_,B_,-i_]:>1,
n[A_,B_,i_]n[B_,A_,-i_]:>-1};


(*counting acceleration order*)
DefConstantSymbol[accel,PrintAs->"a"]


hideAccel[ex_]:=ex/.{accel->1}
showAccel[ex_]:=hideAccel[ex]/.{T_[wl[A_,n_],i___]:>accel^n T[wl[A,n],i]}/.{x[wl[A_,n_],i_]:>accel^(-Min[1,n]) x[wl[A,n],i]}


(*counting spin orders*)
DefConstantSymbol[SO]
DefConstantSymbol[SO1]
DefConstantSymbol[SO2]


showSOsimple[e_]:=hideSO[e]/.{S[X___]:>SO S[X],Sv[X___]:>SO Sv[X],Ssq[X__]:>SO^2 Ssq[X],
Spart[x_]:>SO Spart[x],SSpart[x_]:>SO^2SSpart[x]}
showSO[ex_]:=showSOsimple[ex]/.{S[wl@1,i__]:>SO1 S[wl@1,i],S[wl@2,i__]:>SO2 S[wl@2,i],Sv[wl@1,i__]:>SO1 Sv[wl@1,i],Sv[wl@2,i__]:>SO2 Sv[wl@2,i],Ssq[wl@1,i__]:>SO1^2 Ssq[wl@1,i],Ssq[wl@2,i__]:>SO2^2 Ssq[wl@2,i]}
hideSO[ex_]:=ex/.{SO->1,SO1->1,SO2->1}


PMpart[expr_]:=(expr//showSO)/.{SO->0}
SOpart[expr_]:=Coefficient[(expr//showSO)/.SO2->0,SO1,1]
SOpartF[expr_]:=Coefficient[(expr//showSO)/.SO2->0,SO1,1]+Coefficient[(expr//showSO)/.SO1->0,SO2,1]
S1S2part[expr_]:=Coefficient[Coefficient[expr//showSO,SO1,1],SO2,1]
S1S1part[expr_]:=Coefficient[(expr//showSO)/.SO2->0,SO1,2]
S1S1partF[expr_]:=Coefficient[(expr//showSO)/.SO2->0,SO1,2]+Coefficient[(expr//showSO)/.SO1->0,SO2,2]
cutMass[ex_]:=ex-(ex/.SO->0)


(*exchange of labels*)
xChange[A_,B_][ex_]:=ex/.{A->B,B->A}
mirror[A_,B_][ex_]:=ex+xChange[A,B][ex]
mirror12[ex_]:=ex//mirror[wl[1],wl[2]]//showSO


(*PN power counting parameter*)
DefConstantSymbol[cInv,PrintAs->"(\!\(\*SuperscriptBox[\(c\), \(-1\)]\))"]
(*cut at PN and/or spin order*)
$MaxPNOrder=8;
$MaxSpinOrder=2;
cutMore[o_][e_]:=Series[e,{cInv,0,$MaxPNOrder-o}]//Normal
cutSpin[e_]:=Series[e,{SO,0,$MaxSpinOrder}]//Normal
cut4PN[ex_]:=ex-cInv^8 Coefficient[ex//PMpart,cInv,8];
cut3PN[ex_]:=cut4PN[ex]-cInv^6 Coefficient[ex//PMpart,cInv,6];
cut[e_]:=e//cutMore[0]//cutSpin//cut3PN


(*dimensional regulator d=3+\[Epsilon]d*)
DefConstantSymbol[\[Epsilon]d]
(*aux simplifications*)
simpF[f_][e_]:=Collect[e/.xRule/.mRule,{cInv,SO,SO1,SO2,accel,G,Scalar[r[__]],Scalar[m[__]],Scalar[CES2[__]],\[Epsilon]d,Gamma[_],\[Pi]^_},ScreenDollarIndices@f@ToCanonical@ContractMetric@#&]/.xRule
simp[e_]:=simpF[PutScalar][e]
simpNS[e_]:=simpF[NoScalar][e]
simpFinal[e_]:=simp[e//showSO//showAccel]


(*convert sum of terms to list and vice versa*)
PlusToList[e_Plus]:=List@@e
PlusToList[e_]:={e}
ListToPlus[l_List]:=Plus@@l


(*put head on each term in a sum*)
putHead[h_][e_]:=ListToPlus[h/@PlusToList@Expand@e]


(*apply transformation term by term, with optional status bar*)
termbyterm[transfo_,bar_:False][e_]:=Module[{terms, numterms, count = 0, result, time},
terms=PlusToList@e;
numterms=Length[terms];
If[bar,
Print["Number of terms: ",numterms];
Print[ProgressIndicator[Dynamic[count],{0,numterms}]];];
time=Timing[result=Plus@@((count++;transfo[#])&/@terms);]//First;
If[bar,Print["Time: ",time," s"];];
result]


(*timing*)
Needs["Units`"]
timeIt[ex_]:=Module[{time},
time=First@Timing[ex];
timing==If[time<60.0,
Round[time,0.1]Second, 
If[time<60.0 60.0,
Round[time/60,0.1] Minute,
Round[time/60/60,0.1] Hour ] ] ]
SetAttributes[timeIt,HoldFirst]


(* ::Subchapter::Closed:: *)
(*FeynRul*)


(* ::Subsection::Closed:: *)
(*definitions*)


(*fields. notice: 2nd label is time derivative*)
DefTensor[\[Phi][LI[],LI[]],{Md,t}]
DefTensor[A[LI[],LI[],i],{Md,t}]
DefTensor[\[Sigma][LI[],LI[],i,j],{Md,t},Symmetric[{i,j}]]


(*Dirac delta of time points including time derivatives*)
DefTensor[\[Delta]t[LI[],LI[],LI[],LI[]],Md]


(*Fourier vectors*)
DefTensor[k[LI[],i],Const]
(*symbolic scalar representation*)
DefTensor[ks[LI[]],Const]


(*head for differential of integrals*)
DefInertHead[dd]


(*Exp including the I*)
DefScalarFunction[e]
Derivative[n_][e][x_]:=I^n e[x]


(*Dirac delta head*)
DefInertHead[D\[Delta]]


(*shorthand for delta of k vectors*)
\[Delta]k[A__]:=D\[Delta]@(Plus@@(ks[pt@#]&/@{A}))


(*head for bare propagator*)
DefInertHead[prop]


(* ::Subsection::Closed:: *)
(*vertices manifold*)


DefManifold[Vertices,\[Infinity],{A1,A2,A3,A4,A5,A6,A7,A8,B1}]


(*propagators*)
DefTensor[\[Phi]\[Phi][LI[],LI[]],Vertices]
DefTensor[AA[LI[],LI[]],Vertices]
DefTensor[\[Sigma]\[Sigma][LI[],LI[]],Vertices]


(*propagator time insertions are treated as vertices*)
DefTensor[\[Phi]X\[Phi][LI[],LI[]],Vertices]
DefTensor[AXA[LI[],LI[]],Vertices]
DefTensor[\[Sigma]X\[Sigma][LI[],LI[]],Vertices]


(*bulk/field vertices*)
DefTensor[\[Phi]\[Phi]\[Phi][LI[],LI[],LI[]],Vertices]
DefTensor[\[Phi]\[Phi]A[LI[],LI[],LI[]],Vertices]
DefTensor[\[Phi]\[Phi]\[Sigma][LI[],LI[],LI[]],Vertices]
DefTensor[\[Phi]AA[LI[],LI[],LI[]],Vertices]
DefTensor[\[Phi]A\[Sigma][LI[],LI[],LI[]],Vertices]
DefTensor[AAA[LI[],LI[],LI[]],Vertices]
DefTensor[AA\[Sigma][LI[],LI[],LI[]],Vertices]
DefTensor[\[Phi]4[LI[],LI[],LI[],LI[]],Vertices]
DefTensor[\[Phi]\[Phi]AA[LI[],LI[],LI[],LI[]],Vertices]


(*worldline vertices*)
DefTensor[pk[LI[]],Vertices]
DefTensor[p\[Phi][LI[],LI[]],Vertices]
DefTensor[p\[Phi]\[Phi][LI[],LI[],LI[]],Vertices]
DefTensor[p\[Phi]3[LI[],LI[],LI[],LI[]],Vertices]
DefTensor[p\[Phi]4[LI[],LI[],LI[],LI[],LI[]],Vertices]
DefTensor[pA[LI[],LI[]],Vertices]
DefTensor[p\[Phi]A[LI[],LI[],LI[]],Vertices]
DefTensor[p\[Phi]\[Phi]A[LI[],LI[],LI[],LI[]],Vertices]
DefTensor[pAA[LI[],LI[],LI[]],Vertices]
DefTensor[p\[Sigma][LI[],LI[]],Vertices]
DefTensor[pA\[Sigma][LI[],LI[],LI[]],Vertices]
DefTensor[p\[Phi]\[Sigma][LI[],LI[],LI[]],Vertices]


(* ::Subsection::Closed:: *)
(*prepare rules*)


(*read Feynman rules from 2 output files, convert to current notation: 
indices, fields, worldline dofs, constants, time derivatives*)
simpFR[e_]:=Collect[e,{cInv,SO,SO1,SO2,accel,Scalar[CES2[__]]},Together]
SetDirectory[NotebookDirectory[]];
importRules[file_]:=Get[file]/.{
m->m[wl[1]],CES2->CES2[wl[1]],v[i_]:>x[wl[1,1],i],a1[i_]:>x[wl[1,2],i],S[i__]:>S[wl[1,0],i],
\[Phi][i___]:>\[Phi][pt[0,0],i],A[i___]:>A[pt[0,0],i],\[Sigma][i___]:>\[Sigma][pt[0,0],i]}/.
MakeRule[{S[wl[1,0],i,j] S[wl[1,0],-i,-j],2 Ssq[wl[1,0]]}//Evaluate]//.{
ParamD[t,p___]@T_[A___]:>ParamD[p]@incDt@T[A]}//showSOsimple//simpFR//simp
frules=importRules["frules_field.dat.m"];
wlrules=importRules["frules_wl.dat.m"];


(*adjust PN count from Feynman rules files: 
vertices are PNcounted only according to the matter dofs*)
adjustPNCount[\[Phi]o_,Ao_,\[Sigma]o_][ex_]:=ex/cInv^(0\[Phi]o+1Ao+2\[Sigma]o)


(*extract vertex with certain powers of the fields*)
DefConstantSymbol[Torder]
TensorCoeff[T_,o_][ex_]:=Coefficient[ex/.T[i___]:>Torder T[i],Torder,o]
FieldCoeff[\[Phi]o_,Ao_,\[Sigma]o_][ex_]:=ex//TensorCoeff[\[Phi],\[Phi]o]//TensorCoeff[A,Ao]//TensorCoeff[\[Sigma],\[Sigma]o]


(*enumerate fields of the same type in a vertex using the point label*)
enumerField[T_][ex_]:=ListToPlus[Module[{count=1},
#//.{
T[pt[0],i___]^n_:>T[pt[0],i]^(n-1)T[pt[count++],i],
T[pt[0],i___]:>T[pt[count++],i]
}]&/@PlusToList[Expand[NoScalar[ex]]]]
enumerFields[ex_]:=ex//enumerField[\[Phi]]//enumerField[A]//enumerField[\[Sigma]]


(*permute same field in a vertex: summing all possible contractions of the vertex.
must be called after enumerFields and before offsetFields*)
permuteList[n_]:=Thread[Range[n]->#]&/@Permutations[Range[n]]
permuteField[T_,n_][ex_]:=Plus@@(ex/.{T[pt[p_],i___]:>T[pt[p/.#],i]}&/@permuteList[n])
permuteFields[\[Phi]o_,Ao_,\[Sigma]o_][ex_]:=ex//permuteField[\[Phi],\[Phi]o]//permuteField[A,Ao]//permuteField[\[Sigma],\[Sigma]o]


(*offset label of fields of different type, so that every field has a different label*)
offsetFields[\[Phi]o_,Ao_,\[Sigma]o_][ex_]:=ex/.{A[pt[nA_],i___]:>A[pt[nA+\[Phi]o],i],\[Sigma][pt[nA_],i___]:>\[Sigma][pt[nA+\[Phi]o+Ao],i]}


(*apply sequentially to collect all vertex contractions*)
vertexContractions[\[Phi]o_,Ao_,\[Sigma]o_][ex_]:=ex//enumerFields//permuteFields[\[Phi]o,Ao,\[Sigma]o]//offsetFields[\[Phi]o,Ao,\[Sigma]o]


(*prefactors for each field in vertex*)
fieldFactors[\[Phi]o_,Ao_,\[Sigma]o_][ex_]:=ex*Module[{P},Product[dd[ks[pt@P]]\[Delta]t[pt[P,0],pt[0,0]],{P,\[Phi]o+Ao+\[Sigma]o}]]


(*Fourier spatial derivatives. 
call after vertexContractions*)
fourierCD[ex_]:=ex//.{
CD[i_]@T_[pt[A_,n_],j___]:>I k[pt@A,i]T[pt[A,n],j],
CD[j_]@k[A_,i_]->0}


(*flip time derivatives from fields to \[Delta]t.
call after fieldFactors and fourierCD*)
flipdt[ex_]:=(ex//simp//NoScalar)//.{
\[Delta]t[X___,pt[A_,nA_],Y___]T_[pt[A_,n_?Positive],i___]:>-\[Delta]t[X,pt[A,nA+1],Y]T[pt[A,n-1],i]
}//ScreenDollarIndices


(*put all together: generic vertex preparation*)
prepareVertex[\[Phi]o_,Ao_,\[Sigma]o_][ex_]:=ex//FieldCoeff[\[Phi]o,Ao,\[Sigma]o]//adjustPNCount[\[Phi]o,Ao,\[Sigma]o]//vertexContractions[\[Phi]o,Ao,\[Sigma]o]//fourierCD//fieldFactors[\[Phi]o,Ao,\[Sigma]o]//flipdt//simpNS


(*replace points to names in LHS of vertexRules, see below*)
replacePoints[ex_]:=ex/.{pt[1]->pt[A1],pt[2]->pt[A2],pt[3]->pt[A3],pt[4]->pt[A4]}


(*special preparation of worldline vertex: 
e-factors and replace bulk point by worldline point*)
wlvertex[\[Phi]o_,Ao_,\[Sigma]o_]:=Module[{P,B,j},
Product[e[k[pt@P,j]x[wl[B,0],-j]],{P,\[Phi]o+Ao+\[Sigma]o}]
prepareVertex[\[Phi]o,Ao,\[Sigma]o][wlrules]/.{pt[0]->wl[B],wl[1]->wl[B]}//replacePoints]


(*special preparation of bulk/field vertex: momentum conservation*)
blvertex[\[Phi]o_,Ao_,\[Sigma]o_]:=Module[{P},
D\[Delta]@Sum[ks[pt@P],{P,\[Phi]o+Ao+\[Sigma]o}]
prepareVertex[\[Phi]o,Ao,\[Sigma]o][frules]//replacePoints]


(*prepare end vertex so that time derivatives drop on it*)
endVertex[ex_]:=ex//.{
\[Delta]t[wl[A_,nA_],pt[B_,nB_?Positive]]:>(-1)^nB \[Delta]t[wl[A,nA+nB],pt[B,0]],
\[Delta]t[pt[B_,nB_?Positive],wl[A_,nA_]]:>(-1)^nB \[Delta]t[pt[B,0],wl[A,nA+nB]]}


(* ::Subsection::Closed:: *)
(*propagators*)


dtld=d-2;
cd=2*(d-1)/dtld;


P[i_,j_,k_,l_]:=1/2(delta[i,k] delta[j,l]+delta[i,l] delta[j,k]+Together[2-cd] delta[i,j] delta[k,l])


propagatorRules={
\[Phi]\[Phi][pt@A1_,pt@A2_]\[Phi][pt[A1_,0]]\[Phi][pt[A2_,0]]:>4/cd 4\[Pi] G \[Delta]k[A1,A2]\[Delta]t[pt[A1,0],pt[A2,0]]prop[(ks@pt@A1)^2],
AA[pt@A1_,pt@A2_]A[pt[A1_,0],i_]A[pt[A2_,0],j_]:>-16\[Pi] G delta[i,j]\[Delta]k[A1,A2]\[Delta]t[pt[A1,0],pt[A2,0]]prop[(ks@pt@A1)^2],
\[Sigma]\[Sigma][pt@A1_,pt@A2_]\[Sigma][pt[A1_,0],i1_,i2_]\[Sigma][pt[A2_,0],j1_,j2_]:>32\[Pi] G P[i1,i2,j1,j2]\[Delta]k[A1,A2]\[Delta]t[pt[A1,0],pt[A2,0]]prop[(ks@pt@A1)^2]
};


(* ::Subsection::Closed:: *)
(*vertices*)


vertexRules={
(*propagator insertions treated as bulk vertices*)
\[Phi]X\[Phi][pt@A1_,pt@A2_]:>cd/4 2cInv^2/(8\[Pi] G) dd[ks@pt@A1]dd[ks@pt@A2]\[Delta]k[A1,A2]\[Delta]t[pt[A1,1],pt[A2,1]]\[Phi][pt[A1,0]]\[Phi][pt[A2,0]],
AXA[pt@A1_,pt@A2_]:>-2cInv^2/(32\[Pi] G) dd[ks@pt@A1]dd[ks@pt@A2]\[Delta]k[A1,A2]\[Delta]t[pt[A1,1],pt[A2,1]]Module[{i},A[pt[A1,0],i]A[pt[A2,0],-i]],
\[Sigma]X\[Sigma][pt@A1_,pt@A2_]:>2cInv^2/(128\[Pi] G) dd[ks@pt@A1]dd[ks@pt@A2]\[Delta]k[A1,A2]\[Delta]t[pt[A1,1],pt[A2,1]]Module[{i,j},2\[Sigma][pt[A1,0],i,j]\[Sigma][pt[A2,0],-i,-j]-\[Sigma][pt[A1,0],i,-i]\[Sigma][pt[A2,0],j,-j]],
(*field vertices*)
\[Phi]\[Phi]\[Phi][pt@A1_,pt@A2_,pt@A3_]->blvertex[3,0,0],
\[Phi]\[Phi]A[pt@A1_,pt@A2_,pt@A3_]->blvertex[2,1,0],
\[Phi]\[Phi]\[Sigma][pt@A1_,pt@A2_,pt@A3_]->blvertex[2,0,1],
\[Phi]AA[pt@A1_,pt@A2_,pt@A3_]->blvertex[1,2,0],
\[Phi]A\[Sigma][pt@A1_,pt@A2_,pt@A3_]->blvertex[1,1,1],
AAA[pt@A1_,pt@A2_,pt@A3_]->blvertex[0,3,0],
AA\[Sigma][pt@A1_,pt@A2_,pt@A3_]->blvertex[0,2,1],
\[Phi]4[pt@A1_,pt@A2_,pt@A3_,pt@A4_]->blvertex[4,0,0],
\[Phi]\[Phi]AA[pt@A1_,pt@A2_,pt@A3_,pt@A4_]->blvertex[2,2,0],
(*worldline vertices*)
pk[wl@B_]->wlvertex[0,0,0],
p\[Phi][wl@B_,pt@A1_]->endVertex@wlvertex[1,0,0],
p\[Phi]\[Phi][wl@B_,pt@A1_,pt@A2_]->wlvertex[2,0,0],
p\[Phi]3[wl@B_,pt@A1_,pt@A2_,pt@A3_]->wlvertex[3,0,0],
p\[Phi]4[wl@B_,pt@A1_,pt@A2_,pt@A3_,pt@A4_]->wlvertex[4,0,0],
pA[wl@B_,pt@A1_]->endVertex@wlvertex[0,1,0],
p\[Phi]A[wl@B_,pt@A1_,pt@A2_]->wlvertex[1,1,0],
p\[Phi]\[Phi]A[wl@B_,pt@A1_,pt@A2_,pt@A3_]->wlvertex[2,1,0],
pAA[wl@B_,pt@A1_,pt@A2_]->wlvertex[0,2,0],
p\[Sigma][wl@B_,pt@A1_]->endVertex@wlvertex[0,0,1],
p\[Phi]\[Sigma][wl@B_,pt@A1_,pt@A2_]->wlvertex[1,0,1],
pA\[Sigma][wl@B_,pt@A1_,pt@A2_]->wlvertex[0,1,1]
}/.{(L_->R_):>(L:>ReplaceDummies[R/.{pt@0->pt@Unique[]}])};


(*cut worldline vertex according to spin order*)
SpinProjectorList={mpart,Spart,SSpart};
DefInertHead/@SpinProjectorList;
partRules={
mpart[ex_]:>(ex/.SO->0),
Spart[ex_]:>Coefficient[ex,SO,1],
SSpart[ex_]:>Coefficient[ex,SO,2]
};
(*used only in FeynGen*)
SpinProjectorQ[sym_]:=MemberQ[SpinProjectorList,sym];


(* ::Subchapter::Closed:: *)
(*FeynInteg*)


(* ::Subsection::Closed:: *)
(*time derivative*)


(*similar to xTensor*)
dt[A_][sum_Plus]:=Map[dt[A],sum]
dt[A_][x_ y_]:=dt[A][x]y+x dt[A][y]
multiD[der_,f_[args__]]:=(Derivative[Sequence@@#][f][args]&/@IdentityMatrix[Length[{args}]]).(der/@ReplaceDummies/@{args})
dt[A_][f_?ScalarFunctionQ[args___]]:=multiD[dt[A],f[args]]
dt[A_][Scalar[expr_]]:=dt[A][ReplaceDummies[expr]]
dt[A_][_?ConstantQ]=0;


(*additional rules*)
dt[A_][H_?InertHeadQ[args___]]:=multiD[dt[A],H[args]]
dt[A_][_?ConstTensorQ[___]]=0;
dt[A_][_?xTensorQ[B___]]/;FreeQ[{B},A]:=0


(*flip dt on \[Delta]t for partial integrations. must be applied before the main rule*)
dt[p@A_][\[Delta]t[X___,pdt[A_,n_],Y___]]:=-\[Delta]t[pdt[A,n],addDt[1][X,Y]]


(*main rule: increases time derivative label*)
dt[p@A_][T_[pdt[A_,n_],i___]]:=T[pdt[A,n+1],i]


(*n-times time derivative*)
dtn[A_,n_][ex_]:=Nest[dt[A],ex,n]


(*define time derivatives of r and xRel. 
not needed for integration, but needed for total time derivatives in comparisons*)
dt[A_][xRel[A_,B_,i_]]:=x[A,td[1],i]
dt[B_][xRel[A_,B_,i_]]:=-x[B,td[1],i]
dt[A_][r[A_,B_]]:=Module[{i},Scalar[xRel[A,B,i]x[A,td[1],-i]]/r[A,B]]
dt[B_][r[A_,B_]]:=Scalar[xRel[B,A,i]x[B,td[1],-i]]/r[A,B]
(*total time derivative with respect to "both" worldline times*)
dt12[ex_]:=dt[wl@1][ex]+dt[wl@2][ex]


(* ::Subsection::Closed:: *)
(*time integrations*)


(*head for time integration: useful for formulating partial integration*)
DefInertHead[intT,LinearQ->True]
intT[0]=0;


(*flip time derivatives on \[Delta]t until they reach endpoints on a worldline*)
flipon\[Delta]t[ex_]:=ex//.{
intT[\[Delta]t[X1___,pdt[A_,n1_?Positive],Y1___]\[Delta]t[X2___,pdt[A_,n2_],Y2___]e_]:>putHead[intT][(-1)^n1 \[Delta]t[X1,pdt[A,0],Y1]dtn[p@A,n1][\[Delta]t[X2,pdt[A,n2],Y2]e]]}


(*partial integration at endpoints*)
partialIntEndpoints[ex_]:=ex//.{
intT[\[Delta]t[X___,wl[A_,n_?Positive],Y___]e_]:>putHead[intT][(-1)^n \[Delta]t[X,wl[A,0],Y]dtn[wl@A,n]@e]}


(*symbol to glue worldline points: defined by "removeIntT" below*)
DefTensor[glue[LI[],LI[]],Const]
SetAttributes[glue,Orderless]
(*remove product of \[Delta]t, glue worldline points to worldline, remove intT head*)
removeIntT[ex_]:=ex/.{\[Delta]t[pdt[_,0],pdt[_,0]]->1}/.{\[Delta]t[X___]:>ERROR[" intT failed "\[Delta]t[X]]}//.{
intT[glue[wl_,pts__]e_]:>intT[e/.(#->wl&/@{pts})]
}/.{intT->Identity}


(*main function for time integrations*)
integrate\[Delta]t[e_]:=putHead[intT][e]//flipon\[Delta]t//partialIntEndpoints//removeIntT


(* ::Subsection::Closed:: *)
(*integration over Dirac deltas of momenta*)


(*head for integrals*)
DefInertHead[Int,LinearQ->True]


(*simplify and order propagators*)
simpProp[e_]:=e/.prop[ex_]:>prop[ex//Simplify]/.{dd[ks@A_]prop[(X__-ks@A_)^2]:>dd[ks@A]prop[(ks@A-Plus[X])^2]}
(*expand integrals*)
expandInt[ex_]:=ex/.{
Int[e_]:>Int@ContractMetric@Expand@expandInt@e}//.{
Int[Verbatim[Times][L___,T_,R___]]/;And[FreeQ[T,ks],FreeQ[T,k]]:>T Int[L R],
Int[e_]/;Or[FreeQ[e,dd],And[FreeQ[e,ks],FreeQ[e,k]]]:>e,
Int[]->1
}//simpProp
(*head on terms in Int*)
prepareIntegrals[ex_]:=putHead[Int][ex]//expandInt


(*integrate over Dirac deltas*)
intD\[Delta][e_,modF_:Identity]:=e//.{Int[dd[X_]D\[Delta][s_]ex_]/;MemberQ[s,X,\[Infinity]]:>Int[ex/Abs[D[s,X]]/.modF[First[Solve[s==0,X]]]]}
(*specialize to integrals involving \[Delta]k*)
ksTok[{A_->B_}]:={(A/.ks->(k[#,i_]&)):>(B/.ks->(k[#,i]&))}
integrate\[Delta]k[ex_]:=intD\[Delta][prepareIntegrals[ex],(Join[#,ksTok[#]])&]


(* ::Subsection::Closed:: *)
(*factorizing integrals*)


(*integral of single variable, used in intermediate transformations*)
DefInertHead[int1,LinearQ->True]


(*pull independent variables out of the integral*)
expelIndep[ex_]:=ex//.{int1[Verbatim[Times][L___,T_,R___],dd[ks@A_]]/;And[FreeQ[T,ks@A],FreeQ[T,k[A,___]]]:>T int1[L R,dd[ks@A]]}
removeint1[ex_]:=ex//.int1[i_,x_]:>Int[x i]
(*convert to integral over single variables*)
toSingleInt[ex_]:=ex//.{
Int[dd[ks@A_]e_]:>Int[int1[e,dd[ks@A]]//expelIndep]
}/.Int->Identity//removeint1
(*to multiple Int*)
toMultiInt[ex_]:=ex//.{Int[e1_ Int[e2_]]:>Int[e1 e2]}


(*try to factorize integrals by converting to single integrations and back*)
tryFactorInt[ex_]:= ex//toSingleInt//toMultiInt
factorIntegrals[ex_]:=ex//.{
Int[dd[ks@A_]dd[ks@B_]e_]:>tryFactorInt@Int[dd[ks@A]dd[ks@B]e]}


(* ::Subsection::Closed:: *)
(*changing integration variables*)


(*change of integration variable*)
changeIntVRule[ksN_][ksRule_]:=Join[
ksRule/.{(L_->R_):>(dd[L]->Abs[D[R/.ksRule,ksN]]dd[ksN])},
ksTok[ksRule],ksRule]
changeIntVar[ex_,P_,v_]:=Module[{Pn=pt@Unique[]},
ex/.changeIntVRule[ks@Pn]@First@Solve[v==ks@Pn,ks@P]//expandInt]


(*simplify exponents*)
simpExp[ex_]:=ex//.{Int[e1_ Int[e2_]]:>Int[e1 e2]}//.{e[X_]e[Y_]:>e[
Collect[(X+Y//NoScalar//ToCanonical//Simplify//ScreenDollarIndices)/.xRule,xRel[__]]//Scalar]}
(*change integration variable to Fourier k*)
changeIntVtoFourierk[expr_]:=simpExp[expr]/.{
Int[dd[ks@pt@n_]e@Scalar[kk_ xRel[X__]]ex___]/;MemberQ[kk,k[pt@n,_],\[Infinity]]:>changeIntVar[Int[dd[ks@pt@n]e@Scalar[kk xRel[X]]ex],pt@n,kk/.{k[pt@l_,_]:>ks[pt@l]}],
Int[dd[ks@pt@n_]e[-Scalar[kk_ xRel[X__]]]ex___]/;MemberQ[{kk},k[pt@n,_],\[Infinity]]:>changeIntVar[Int[dd[ks@pt@n]e[-Scalar[kk xRel[X]]]ex],pt@n,-kk/.{k[pt@l_,_]:>ks[pt@l]}]}


(*variable changes needed for nesting integrals*)
nestChangeVar[ex_]:=ex//.{Int[dd[ks@A_]prop[(ks@A_+X_)^2]prop[(ks@A_+X_+Y__)^2]e_]:>
changeIntVar[Int[dd[ks@A]prop[(ks@A+X)^2]prop[(ks@A+X+Y)^2]e],A,ks@A+X]}
oneLoopChangeVar[ex_]:=simpProp[ex]//.{Int[dd[ks@A_]prop[(ks@A_+X_)^2]prop[(ks@A_+Y_)^2]kk_]:>
changeIntVar[Int[dd[ks@A]prop[(ks@A+X)^2]prop[(ks@A+Y)^2]kk],A,ks@A+X]}


(* ::Subsection::Closed:: *)
(*nesting integrals*)


(*check for propagators with certain k*)
nopropwith[A_][e_]:=FreeQ[Reap[e/.prop->Sow],ks@A]
(*nest loop intergrals*)
nestLoops[ex_]:=nestChangeVar[ex]//.{
Int[dd[ks@A_]dd[ks@B_]prop[p1_]prop[p2_]e_]/;And[MemberQ[p1,ks@A,\[Infinity]],MemberQ[p2,ks@A,\[Infinity]],nopropwith[A][e]]:>Int[dd[ks@B](int1[prop[p1]prop[p2]e,dd[ ks@A]]//expelIndep//removeint1//oneLoopChangeVar)]}


(*nest first integral with exp*)
nestExp[ex_]:=ex/.{
Int[dd[ks@A_]dd[B_]e[E_]expr_]/;MemberQ[E,k[A,_],\[Infinity]]:>Int[dd[ks@A]e[E]nestLoops@tryFactorInt@Int[dd[B]expr]]}


(*try to nest integrals*)
nestIntegrals[ex_]:=expandInt[ex//changeIntVtoFourierk]//.{
Int[dd[ks@A_]dd[ks@B_]e_]:>(Int[dd[ks@A]dd[ks@B]e]//nestExp//nestLoops//simpProp)}


(* ::Subchapter::Closed:: *)
(*NLoop: generate master integrals*)


(* ::Subsection::Closed:: *)
(*definitions and tools for derivation*)


(*exponents on propagators*)
DefConstantSymbol[\[Alpha]]
DefConstantSymbol[\[Beta]]


(*nicer print and short for the Gamma function*)
\[CapitalGamma]=Gamma;
Unprotect[Gamma];
PrintAs[Gamma]^="\[CapitalGamma]";
Protect[Gamma];


(*spatial derivatives to generate tensor integrals*)
Dx[i_][sum_Plus]:=Map[Dx[i],sum]
Dx[i_][x_ y_]:=Dx[i][x]y+x Dx[i][y]
Dx[i_][f_?ScalarFunctionQ[args___]]:=multiD[Dx[i],f[args]]
Dx[i_][Scalar[x_]]:=Dx[i][ReplaceDummies[x]]
Dx[i_][_?ConstantQ]=0;


(*additional rules*)
IndependentOfxQ[e_]:=FreeQ[e,x]
Dx[i_][x_?IndependentOfxQ]:=0
Dx[i_][x[A_,j_]]:=delta[i,j]


(* ::Subsection::Closed:: *)
(*Fourier master integrals: I*)


(*scalar master integral I*)
masterI=Block[{A,B},dd[ks@p@A]e[Scalar[k[LI@A,i]x[LI@B,-i]]]/Scalar[k[LI@A,i]k[LI@A,-i]]^\[Alpha]->1/(4\[Pi])^(d/2)\[CapitalGamma][d/2-\[Alpha]]/\[CapitalGamma][\[Alpha]](Scalar[x[LI@B,i]x[LI@B,-i]]/4)^(\[Alpha]-d/2)];


(*iteration operator for I*)
Iiterate[i_][ex_]:=Dx[i][ex]/I
Iiterate[i_][x_->y_]:=Iiterate[i][x]->Iiterate[i][y]


(*simplification of I*)
simpI[e_]:=Collect[e//ToCanonical,{Gamma[\[Alpha]],\[Pi]^_,Scalar[_]},FullSimplify]
simpI[x_->y_]:=(simpI[x]->simpI[y])


(*iteratively generate tensor integrals up to order 6*)
{masterI};
Append[%,Iiterate[i1]@Last[%]//simpI];
Append[%,Iiterate[i2]@Last[%]//simpI];
Append[%,Iiterate[i3]@Last[%]//simpI];
Append[%,Iiterate[i4]@Last[%]//simpI];
Append[%,Iiterate[i5]@Last[%]//simpI];
Append[%,Iiterate[i6]@Last[%]//simpI];
masterIvec=%;


(*formulate replacement rules for master integrals*)
masterIrules=masterIvec/.{(LHS_->RHS_):>
Int[LHS/.{Scalar[k[p@A_,i_]k[p@A_,-i_]]:>1/prop[(ks@p@A)^2]}//PowerExpand]->RHS}/.{(LHS_->RHS_):>((ToExpression[StringReplace[ToString[InputForm[LHS]],{"A"->"A_","x"->"xRel_","LI[B]"->"C__"}]])-> (ToExpression[StringReplace[ToString[InputForm[RHS]],{"x"->"xRel","LI[B]"->"C"}]]))}/.{(LHS_->RHS_):>((LHS/.{i->j_,i1->j1_,i2->j2_,i3->j3_,i4->j4_,i5->j5_,i6->j6_})->(RHS/.{i->j,i1->j1,i2->j2,i3->j3,i4->j4,i5->j5,i6->j6}))};
(*special cases like \[Alpha]=1 should be provided explicitly for patterns to match*)
fourierIntegrals=Join[
masterIrules/.\[Alpha]->1,
masterIrules
]/.{(L_->R_):>((L/.{\[Alpha]->aa_})->(R/.{\[Alpha]->aa}))};


(* ::Subsection::Closed:: *)
(*one-loop master integrals: J*)


(*scalar master integral J*)
masterJ=Block[{A,B},dd[ks@p@A]1/Scalar[k[p@A,i]k[p@A,-i]]^\[Alpha] /Scalar[(k[p@A,i]+x[p@B,i])(k[p@A,-i]+x[p@B,-i])]^\[Beta]->1/(4\[Pi])^(d/2)\[CapitalGamma][\[Alpha]+\[Beta]-d/2]/\[CapitalGamma][\[Alpha]]/\[CapitalGamma][\[Beta]]\[CapitalGamma][d/2-\[Alpha]]\[CapitalGamma][d/2-\[Beta]]/\[CapitalGamma][d-\[Alpha]-\[Beta]]Scalar[x[p@B,i]x[p@B,-i]]^(d/2-\[Alpha]-\[Beta])];


(*iteration operator for J*)
Jiterate[i_][ex_]:=Block[{B},-(1/(2\[Beta]) Dx[i][ex]+(ex/.\[Beta]->\[Beta]+1)x[p@B,i])/.\[Beta]->\[Beta]-1//ContractMetric]
Jiterate[i_][x_->y_]:=Jiterate[i][x]->Jiterate[i][y]


(*simplification of J*)
simpJ[e_]:=Collect[e,{\[Pi]^_,Scalar[_],x[__]},FullSimplify]
simpJ[x_->y_]:=(simpJ[x]->simpJ[y])


(*iteratively generate tensor integrals up to order 6*)
{masterJ};
Append[%,Jiterate[i1]@Last[%]//simpJ];
Append[%,Jiterate[i2]@Last[%]//simpJ];
Append[%,Jiterate[i3]@Last[%]//simpJ];
Append[%,Jiterate[i4]@Last[%]//simpJ];
Append[%,Jiterate[i5]@Last[%]//simpJ];
Append[%,Jiterate[i6]@Last[%]//simpJ];
masterJvec=%;


(*formulate replacement rules for master integrals*)
masterJrules=masterJvec/.{(LHS_->RHS_):>( 
Int[LHS/.{Scalar[k[p@A_,i_]k[p@A_,-i_]]:>1/prop[(ks@p@A)^2],
Scalar[(k[p@A_,-j_]+x[p@B_,-j_])(k[p@A_,j_]+x[p@B_,j_])]:>1/prop[(ks@p@A+ks@p@B)^2]}//PowerExpand]->RHS)}/.{(LHS_->RHS_):>((ToExpression[StringReplace[ToString[InputForm[LHS]],{"A"->"A_","x"->"k_","B"->"A1_"}]])-> (ToExpression[StringReplace[ToString[InputForm[RHS]],{"x"->"k","B"->"A1"}]]))}/.{(LHS_->RHS_):>((LHS//.{i->j_,i1->j1_,i2->j2_,i3->j3_,i4->j4_,i5->j5_,i6->j6_})->(RHS/.{i->j,i1->j1,i2->j2,i3->j3,i4->j4,i5->j5,i6->j6,Scalar[k[p@A_,i_]k[p@A_,-i_]]:>1/prop[(ks@p@A)^2]}//PowerExpand))};


(*case of opposite relative sign in the propagtors*)
masterJrules=Join[
masterJrules,
Module[{bl=Pattern[#,Blank[]]&},
masterJrules/.{
prop[(ks[LI[Verbatim@A_]]+ks[LI[Verbatim@A1_]])^2]:>prop[(ks[LI[bl@A]]-ks[LI[bl@A1]])^2],
k[p@A1,i_]:>-k[p@A1,i]
}
]
];
(*special cases like \[Alpha]=1 should be provided explicitly for patterns to match*)
masterJrules=Join[
masterJrules/.{\[Alpha]->1,\[Beta]->1},
masterJrules/.{\[Alpha]->1},
masterJrules/.{\[Beta]->1},
masterJrules
];


masterJshift={Int[dd[ks@A_]prop[(ks@A_)^2]^\[Alpha] prop[(ks@A_+X_+Y__)^2]^\[Beta] kk___]:>Module[{Z,Zrule},
Zrule={ks@p@Z->X+Y};
Int[dd[ks@A]prop[(ks@A)^2]^\[Alpha] prop[(ks@A+ks@p@Z)^2]^\[Beta] kk]/.masterJrules/.Zrule/.ksTok[Zrule]
]};
(*special cases like \[Alpha]=1 should be provided explicitly for patterns to match*)
masterJshift=Join[
masterJshift/.{\[Alpha]->1,\[Beta]->1},
masterJshift/.{\[Alpha]->1},
masterJshift/.{\[Beta]->1},
masterJshift
];


(*collect all master 1-loop integrals*)
oneloopIntegrals=Join[
masterJrules,
masterJshift
]/.{(L_->R_):>((L/.{\[Alpha]->aa_,\[Beta]->bb_})->(R/.{\[Alpha]->aa,\[Beta]->bb}))};


(* ::Subsection::Closed:: *)
(*two-loop integrals*)


(*k derivatives to generate IBP relations*)
Dk[i__][sum_Plus]:=Map[Dk[i],sum]
Dk[i__][x_ y_]:=Dk[i][x]y+x Dk[i][y]
Dk[i__][f_?ScalarFunctionQ[args___]]:=multiD[Dk[i],f[args]]
Dk[i__][Scalar[x_]]:=Dk[i][ReplaceDummies[x]]
Dk[i__][_?ConstantQ]=0;
(*additional rules for k derivatives*)
IndependentOfkQ[A_][e_]:=FreeQ[e,k[A,_]]&&FreeQ[e,ks[A]]
Dk[A_,i_][e_]/;IndependentOfkQ[A][e]:=0
Dk[A_,i_][k[A_,j_]]:=delta[i,j]
Dk[i__][prop[e_^2]]:=-prop[e^2]^2 2Module[{j},(e/.{ks[B_]:>k[B,-j]})Dk[i][e/.{ks[B_]:>k[B,j]}]//ContractMetric//ToCanonical]


(*denoting the three k vectors in the 2-loop by A,B,cc, with cc being the external*)
Clear[A,B,cc]


(*algebraic replacements with the propagators*)
propreps={(k[p@A,-i_]+k[p@B,-i_])(k[p@A,i_]+k[p@B,i_])->1/prop[(ks[p@A]+ks[p@B])^2],k[p@A,-i_](k[p@A,i_]+k[p@B,i_])->1/2(1/prop[ks[p@A]^2]+1/prop[(ks[p@A]+ks[p@B])^2]-1/prop[ks[p@B]^2]),(k[p@A,-i_]+k[p@cc,-i_])(k[p@A,i_]+k[p@B,i_])->1/2(1/prop[(ks[p@A]+ks[p@B])^2]+1/prop[(ks[p@A]+ks[p@cc])^2]-1/prop[(ks[p@B]-ks[p@cc])^2])};


(*simplification where also IrrHead is defined and inserted*)
IrrSimp[ex_,simp_:Simplify]:=Collect[Collect[ex,{IrrHead[_],Int[_],prop[_]^_,prop[_],k[__],\[Delta][__]},IrrHead[simp[#]]&],{IrrHead[_],Int[_],prop[_]^_,prop[_],k[__],\[Delta][__]}]/.{IrrHead[1]->1,IrrHead[a_]IrrHead[b_]:>IrrHead[simp[a b]]}
(*nests external momentum in the numerator out of irreducible two-loop, and futher processes integrals*)
twoloopIntegrals={};
insertKnownMaster[ex_]:=expandInt[ex/.(Join[fourierIntegrals,oneloopIntegrals,twoloopIntegrals]//Dispatch)]
twoloopIntegStep[ex_,simp_:IrrSimp]:=ex//.{Int[Verbatim[Times][L___,k[p@cc,i_],R___]]:>k[p@cc,i]Int[L R]}//factorIntegrals//nestIntegrals//insertKnownMaster//simp
twoloopInteg[ex_,simp_:IrrSimp]:=FixedPoint[twoloopIntegStep[#,simp]&,simp[expandInt[ex]]]


(*main derivation of 2-loop IBP relations*) 
IBP2loop[Ai_List,Bi_List]:=Module[{IrrNum, irrprops,res,i},
(*irreducible 2-loop numerator*)
IrrNum=Times@@(k[p@A,#]&/@Ai)Times@@(k[p@B,#]&/@Bi);
(*irreducible 2-loop denominator factor*)
irrprops=prop[(ks@p@A)^2]prop[(ks@p@B)^2]prop[(ks@p@A+ks@p@B)^2]prop[(ks@p@A+ks@p@cc)^2]prop[(ks@p@B-ks@p@cc)^2];
(*deriving "numerator" terms of integrand*)
res=Dk[p@A,-i][(k[p@A,i]+k[p@B,i])IrrNum*irrprops ]/irrprops/(4-d-Length[Ai]);
res=Collect[res,prop[_]]/.propreps;
res=Collect[res+IrrNum,{prop[_],k[__]},Together]//Expand//ScreenDollarIndices;
If[Length[Ai]+Length[Bi]<2,res=res/.{e_ prop[ks[p@A]^2]:>(e prop[ks[p@A]^2]/.{ks[p@A]->ks[p@A]+ks[p@cc],ks[p@B]->ks[p@B]-ks[p@cc],k[p@A,i_]:>k[p@A,i]+k[p@cc,i],k[p@B,i_]:>k[p@B,i]-k[p@cc,i]})};];
(*processing irreducible 2-loop integrand*)
res=Collect[irrprops*res,{prop[_]},Simplify];
(*reinstating loop integrals*)
res=Int[dd[ks[p@A]]dd[ks[p@B]]res];
(*simplifying irreducible 2-loop integral*)
res=twoloopInteg[res];
res=Collect[res,{Int[_],prop[_]^_,prop[_],k[__],\[Delta][__]}]//.{IrrHead[a_]IrrHead[b_]:>IrrHead[Simplify[a b]]};
res=Collect[res/.{IrrHead[e_]:>e},{Int[_],prop[_]^_,prop[_],k[__],\[Delta][__]},IrrHead];
res=Collect[res,{IrrHead[_],Int[_],prop[_]^_,prop[_],k[__],\[Delta][__]}]/.{IrrHead[e_]:>FullSimplify[FunctionExpand[e]]};
(*formulating the 2-loop integral rules*)
((Int[dd[ks[p@A]]dd[ks[p@B]]IrrNum*irrprops]/.(#->Pattern[#,Blank[]]&/@Ai)/.(#->Pattern[#,Blank[]]&/@Bi))->res)/.Rule->RuleDelayed
/.{(LHS_:> RHS_):>((ToExpression[StringReplace[ToString[InputForm[LHS]],{"A"->"A_","B"->"B_","cc"->"cc_"}]]):>RHS)}
]


(*mirror tensorial IBP relations between two loop momenta*)
mirror2loop[e_]:=e/.{Verbatim[ks[LI@cc_]]->-ks[p@cc_],ks[p@cc]->-ks[p@cc],k[p@cc,i_]:>-k[p@cc,i]}


(*add scalar and tensorial IBP relations to twoloopIntegrals*)
addIBP2loop[inds__]:=Module[{IBP},
IBP=IBP2loop[inds];
AppendTo[twoloopIntegrals,IBP];]
addIBP2loopMirror[inds__]:=Module[{IBP},
IBP=IBP2loop[inds];
AppendTo[twoloopIntegrals,IBP];
AppendTo[twoloopIntegrals,IBP//mirror2loop];]


(*total runtime circa 7hrs*)


addIBP2loop[{},{}];//timeIt


addIBP2loopMirror[{},{j1}];//timeIt


addIBP2loopMirror[{},{j1,j2}];//timeIt


addIBP2loop[{i1},{j1}];//timeIt


addIBP2loopMirror[{},{j1,j2,j3}];//timeIt


addIBP2loopMirror[{i1},{j1,j2}];//timeIt


addIBP2loopMirror[{},{j1,j2,j3,j4}];//timeIt


addIBP2loopMirror[{i1},{j1,j2,j3}];//timeIt


addIBP2loop[{i1,i2},{j1,j2}];//timeIt


addIBP2loopMirror[{},{j1,j2,j3,j4,j5}];//timeIt


addIBP2loopMirror[{i1},{j1,j2,j3,j4}];//timeIt


addIBP2loopMirror[{i1,i2},{j1,j2,j3}];//timeIt


addIBP2loopMirror[{},{j1,j2,j3,j4,j5,j6}];//timeIt


addIBP2loopMirror[{i1},{j1,j2,j3,j4,j5}];//timeIt


addIBP2loopMirror[{i1,i2},{j1,j2,j3,j4}];//timeIt


addIBP2loop[{i1,i2,i3},{j1,j2,j3}];//timeIt


(*check if 2-loop master integrals are fully simplified*)
And@@(FreeQ[#[[2]],Int]&/@twoloopIntegrals)


(*generate more integrals with flipped signs on momenta*)
twoloopIntegralsflip=Module[{bl=Pattern[#,Blank[]]&},
twoloopIntegrals/.{
prop[(ks[LI[Verbatim@B_]]-ks[LI[Verbatim@cc_]])^2]k[LI[Verbatim@B_],i_]:>-prop[(ks[LI[bl@B]]-ks[LI[bl@cc]])^2]k[LI[bl@B],i]
}/.{
prop[(ks[LI[Verbatim@A_]]-ks[LI[Verbatim@cc_]])^2]k[LI[Verbatim@A_],i_]:>-prop[(ks[LI[bl@A]]-ks[LI[bl@cc]])^2]k[LI[bl@A],i]
}/.{
prop[(ks[LI[Verbatim@A_]]+ks[LI[Verbatim@B_]])^2]prop[(ks[LI[Verbatim@B_]]-ks[LI[Verbatim@cc_]])^2]:>prop[(ks[LI[bl@A]]-ks[LI[bl@B]])^2]prop[(ks[LI[bl@B]]+ks[LI[bl@cc]])^2]
}/.{
prop[(ks[LI[Verbatim@B_]]+ks[LI[Verbatim@A_]])^2]prop[(ks[LI[Verbatim@A_]]-ks[LI[Verbatim@cc_]])^2]:>prop[(ks[LI[bl@B]]-ks[LI[bl@A]])^2]prop[(ks[LI[bl@A]]+ks[LI[bl@cc]])^2]
}/.{
(-Int[i_]:>r_):>(Int[i]:>-r)
}
];
twoloopIntegrals=Join[
twoloopIntegrals,
twoloopIntegralsflip
];


(*export to "twoloopintegs" file*)
SetDirectory[NotebookDirectory[]];Put[twoloopIntegrals,"twoloopintegs.dat.m"];


(* ::Subsection::Closed:: *)
(*export all master and reduction integrals*)


SetDirectory[NotebookDirectory[]];
twoloopIntegrals=Get["twoloopintegs.dat.m"];
Put[Join[fourierIntegrals,oneloopIntegrals,twoloopIntegrals],"MasterIntegrals.dat.m"];
Put[masterJrules,"masterJrules.dat.m"];
