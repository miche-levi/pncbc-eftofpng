(* ::Package:: *)

(* ::Title:: *)
(*Package EFTofPNG version 0.99*)


(* ::Chapter:: *)
(*EFTofPNG: Main*)


(* ::Subchapter::Closed:: *)
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


(* load xTensor package *)
Needs["xAct`xTensor`"];
$DefInfoQ = False;
$UndefInfoQ = False;


(* setup d-dimensional manifold and time parameter *)
DefConstantSymbol[d];
DefManifold[Md, d, {
    i, j, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, 
    i16, i17, i18, i19, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, 
    j13, j14, j15, j16, j17, j18, j19, l
}];
(* k is reserved for the Fourier momenta *)
DefMetric[1, \[Delta][-i, -j], CD, {",", "\[PartialD]"}, FlatMetric -> True];
DefParameter[t];
SetOptions[MakeRule, {MetricOn -> All, ContractMetrics -> True}];


(* ::Subsection::Closed:: *)
(*def constants*)


(* gravitational constant *)
DefConstantSymbol[G];


(* a manifold for constant tensors *)
DefManifold[Const, 0, {}];
ConstTensorQ[T_?xTensorQ] := MemberQ[DependenciesOfTensor[T], Const];
ConstTensorQ[_] = False;


(* masses *)
DefTensor[m[LI[]], Const];


(* spin-multipole Wilson coefficients *)
DefTensor[CES2[LI[]], Const];
DefTensor[CBS3[LI[]], Const];
DefTensor[CES4[LI[]], Const];


(* ::Subsection::Closed:: *)
(*def worldline DOFs*)


(* positions, position difference, and distance *)
DefTensor[x[LI[], LI[], i], {Md, t}];
DefTensor[xRel[LI[], LI[], i], {Md, t}];
DefTensor[r[LI[], LI[]], {Md, t}];
SetAttributes[r, Orderless];
DefTensor[n[LI[], LI[], i], {Md, t}];
xRel2n[ex_] := ex/.{xRel[L__, i_] :> n[L, i] * r[L]};
n2xRel[ex_] := ex/.{n[L__, i_] :> xRel[L, i] / r[L]};


(* momenta *)
DefTensor[p[LI[], i], {Md, t}];
DefTensor[phat[LI[], i], {Md, t}];


(* spin tensor, vector, and length square *)
DefTensor[S[LI[], LI[], i, j], {Md, t}, Antisymmetric[{i, j}]];
DefTensor[Sv[LI[], LI[], i], {Md, t}];
DefTensor[Ssq[LI[], LI[]], {Md, t}, PrintAs -> (
    "\!\(\*SuperscriptBox[\(S\), \(2\)]\)")];


(* ::Subsection::Closed:: *)
(*def labels*)


(* ::Text:: *)
(*aux functions and heads for labels of tensors:*)
(*first label for a point, either worldline or bulk/field,*)
(*second label for order of time derivative*)


(* generic head for points *)
p[A_] := LI @ A;
(* head for time derivative *)
td[A_] := LI @ DT @ A;
(* generic point & time derivative *)
pdt[A_, B_] := Sequence[p @ A, td @ B];


(* head for worldline points *)
wl[A_] := p @ WL @ A;
wl[A_, B_] := pdt[WL @ A, B];


(* head for bulk/field points *)
pt[A_] := p @ PT @ A;
pt[A_, B_] := pdt[PT @ A, B];


(* handle time derivative label *)
IncDt[x_[pdt[A_, n_], i___]] := x[pdt[A, n+1], i];
AddDt[n_][A_, td[B_], C___] := Sequence[A, td[B + n], C];


(* ::Subsection::Closed:: *)
(*output labels*)


SetAttributes[InterpretBox, HoldFirst];
InterpretBox[expr_, box_] := InterpretationBox[
    StyleBox[box, AutoSpacing -> False], expr, Editable -> False
];


(* output lables of constants *)
MakeBoxes[m[LI[WL[w_]]], StandardForm] ^:= InterpretBox[
    m[LI[WL[w]]], SubscriptBox[MakeBoxes[m], MakeBoxes[w]]
];
MakeBoxes[CES2[LI[WL[w_]]], StandardForm] ^:= InterpretBox[
    CES2[LI[WL[w]]], SubscriptBox[MakeBoxes[C], GridBox[
        {{MakeBoxes[ES^2], MakeBoxes[w]}}, ColumnSpacings -> 0.05]
    ]
];
MakeBoxes[CBS3[LI[WL[w_]]], StandardForm] ^:= InterpretBox[
    CBS3[LI[WL[w]]], SubscriptBox[MakeBoxes[C], GridBox[
        {{MakeBoxes[BS^3], MakeBoxes[w]}}, ColumnSpacings -> 0.05]
    ]
];
MakeBoxes[CES4[LI[WL[w_]]], StandardForm] ^:= InterpretBox[
    CES4[LI[WL[w]]], SubscriptBox[MakeBoxes[C], GridBox[
        {{MakeBoxes[ES^4], MakeBoxes[w]}}, ColumnSpacings -> 0.05]
    ]
];


(* make all indices Euclidean *)
MakeEuclid[-a_] := a;
MakeEuclid[a_] := a;


(* output labels of x *)
MakeBoxes[x[LI[WL[w_]], LI[DT[0]], i_], StandardForm] ^:= InterpretBox[
    x[LI[WL[w]], LI[DT[0]], i], SubsuperscriptBox[
        MakeBoxes[x], MakeBoxes[w], First[MakeBoxes /@ MakeEuclid /@ {i}]
    ]
];
MakeBoxes[x[LI[WL[w_]], LI[DT[1]], i_], StandardForm] ^:= InterpretBox[
    x[LI[WL[w]], LI[DT[1]], i], SubsuperscriptBox[
        "v", MakeBoxes[w], First[MakeBoxes /@ MakeEuclid /@ {i}]
    ]
];
MakeBoxes[x[LI[WL[w_]], LI[DT[2]], i_], StandardForm] ^:= InterpretBox[
    x[LI[WL[w]], LI[DT[2]], i], SubsuperscriptBox[
        "a", MakeBoxes[w], First[MakeBoxes /@ MakeEuclid /@ {i}]
    ]
];
MakeBoxes[x[LI[WL[w_]], LI[DT[n_]], i_], StandardForm] ^:= Module[
    {nd}, Hold[InterpretBox[
        x[LI[WL[w]], LI[DT[n]], i], SubsuperscriptBox[
            OverscriptBox[MakeBoxes[a], AdjustmentBox[
                GridBox[{{"(", MakeBoxes[nd], ")"}}, ColumnSpacings -> -0.3],
                BoxMargins -> {{-0.3, -0.3}, {0, 0}}]], MakeBoxes[w], 
                AdjustmentBox[GridBox[
                    {MakeBoxes /@ MakeEuclid /@ {i}}, ColumnSpacings -> 0.05
                ],
                BoxBaselineShift -> 0.7]
            ]
        ]
    ]/.nd -> n - 2//ReleaseHold
];


(* output labels of r and n *)
MakeBoxes[xRel[LI[WL[w1_]], LI[WL[w2_]], i_], StandardForm] ^:= InterpretBox[
    xRel[LI[WL[w1]], LI[WL[w2]], i], SubsuperscriptBox[
        MakeBoxes[x], GridBox[
            {{MakeBoxes[w1], MakeBoxes[w2]}}, ColumnSpacings -> 0.05
        ],
        First[MakeBoxes /@ MakeEuclid /@ {i}]
    ]
];
MakeBoxes[x[LI[WL[w1_]], LI[WL[w2_]], i_], StandardForm] ^:= InterpretBox[
    x[LI[WL[w1]], LI[WL[w2]], i], SubsuperscriptBox[
        MakeBoxes[x], GridBox[
            {{MakeBoxes[w1], MakeBoxes[w2]}}, ColumnSpacings -> 0.05
        ],
        First[MakeBoxes /@ MakeEuclid /@ {i}]
    ]
];
MakeBoxes[r[LI[WL[w1_]], LI[WL[w2_]]], StandardForm] ^:= InterpretBox[
    r[LI[WL[w1]], LI[WL[w2]]], SubscriptBox[ 
        MakeBoxes[r], GridBox[
            {{MakeBoxes[w1], MakeBoxes[w2]}}, ColumnSpacings -> 0.05
        ]
    ]
];
MakeBoxes[n[LI[WL[w1_]], LI[WL[w2_]], i_], StandardForm] ^:= InterpretBox[
    n[LI[WL[w1]], LI[WL[w2]], i], SubsuperscriptBox[
        MakeBoxes[n], GridBox[
            {{MakeBoxes[w1], MakeBoxes[w2]}}, ColumnSpacings -> 0.05
        ],
        First[MakeBoxes /@ MakeEuclid /@ {i}] 
    ]
];


(* output labels of S *)
MakeBoxes[S[LI[WL[w_]], LI[DT[0]], i__], StandardForm] ^:= InterpretBox[
    S[LI[WL[w]], LI[DT[0]], i], SubsuperscriptBox[
        MakeBoxes[S], MakeBoxes[w], GridBox[
            {MakeBoxes /@ MakeEuclid /@ {i}}, ColumnSpacings -> 0.05
        ]
    ]
];
MakeBoxes[S[LI[WL[w_]], LI[DT[n_]], i__], StandardForm] ^:= InterpretBox[
    S[LI[WL[w]], LI[DT[n]], i], SubsuperscriptBox[OverscriptBox[
        MakeBoxes[S], AdjustmentBox[GridBox[
            {{"(", MakeBoxes[n], ")"}}, ColumnSpacings -> -0.3
        ], 
        BoxMargins -> {{-0.3, -0.3},{0, 0}}]
    ], 
    MakeBoxes[w], AdjustmentBox[
        GridBox[{MakeBoxes /@ MakeEuclid /@ {i}}, ColumnSpacings -> 0.05],
        BoxBaselineShift -> 0.7
    ]]
];
MakeBoxes[Sv[LI[WL[w_]], LI[DT[0]], i_], StandardForm] ^:= InterpretBox[
    Sv[LI[WL[w]], LI[DT[0]], i], SubsuperscriptBox[ 
        MakeBoxes[S], MakeBoxes[w], GridBox[
            {MakeBoxes /@ MakeEuclid /@ {i}}, ColumnSpacings -> 0.05
        ]
    ]
];
MakeBoxes[Sv[LI[WL[w_]], LI[DT[n_]], i_], StandardForm] ^:= InterpretBox[
    Sv[LI[WL[w]], LI[DT[n]], i], SubsuperscriptBox[OverscriptBox[
        MakeBoxes[S], AdjustmentBox[GridBox[
            {{"(", MakeBoxes[n], ")"}}, ColumnSpacings -> -0.3
        ], 
        BoxMargins -> {{-0.3, -0.3}, {0, 0}}]
    ], 
    MakeBoxes[w], AdjustmentBox[
        GridBox[{MakeBoxes /@ MakeEuclid /@ {i}}, ColumnSpacings -> 0.05],
        BoxBaselineShift -> 0.7
    ]]
];
MakeBoxes[Ssq[LI[WL[w_]], LI[DT[0]]], StandardForm] ^:= InterpretBox[
    Ssq[LI[WL[w]], LI[DT[0]]], SubsuperscriptBox[
        MakeBoxes[S], MakeBoxes[w], AdjustmentBox[
            MakeBoxes[2], BoxBaselineShift -> -0.5
        ]
    ]
];
MakeBoxes[Ssq[LI[WL[w_]], LI[DT[n_?Positive]]], StandardForm] ^:= InterpretBox[
    Ssq[LI[WL[w]], LI[DT[n]]], SubsuperscriptBox[OverscriptBox[
         MakeBoxes[S], AdjustmentBox[GridBox[
             {{"(", MakeBoxes[n], ")"}}, ColumnSpacings -> -0.3
         ],
         BoxMargins -> {{-0.3, -0.1}, {0, 0}}]
    ],
    MakeBoxes[w], AdjustmentBox[MakeBoxes[2], BoxBaselineShift -> -0.5]]
];


(* ::Subsection::Closed:: *)
(*tools*)


(* simplification rules for m, x *)
mRule = {m[A_] :> Scalar[m[A]]};
xRule = {
    x[wl[A_, 0], i_] - x[wl[B_, 0], i_] :> (xRel[wl[A], wl[B], i]/.xRule),
    xRel[A_, B_, i_] :> Order[A, B] * xRel[Sequence @@ Sort[{A, B}], i],
    xRel[A_, B_, i_] * xRel[A_, B_, -i_] :> Scalar[r[A, B]]^2,
    xRel[A_, B_, i_] * xRel[B_, A_, -i_] :> -Scalar[r[A, B]]^2,
    r[A__] :> Scalar[r[A]],
    (r[A__]^n1_)^n2_ :> Scalar[r[A]]^(n1 * n2),
    (Scalar[r[A__]]^n1_)^n2_ :> Scalar[r[A]]^(n1 * n2),
    Log[r[A__]^n_] :> n * Log @ Scalar @ r[A],
    Log[Scalar[r[A__]]^n_] :> n * Log @ Scalar @ r[A],
    n[A_, B_, i_] :> Order[A, B] * n[Sequence @@ Sort[{A, B}], i],
    n[A_, B_, i_] * n[A_, B_, -i_] :> 1,
    n[A_, B_, i_] * n[B_, A_, -i_] :> -1
};


(* counting acceleration order *)
DefConstantSymbol[accel, PrintAs -> "a"];


HideAccel[ex_] := ex/.{accel -> 1};
ShowAccel[ex_] := HideAccel[ex]/.{
    T_[wl[A_, n_], i___] :> accel^n * T[wl[A, n], i]
}/.{
    x[wl[A_, n_], i_] :> accel^(-Min[1, n]) * x[wl[A, n], i]
};


(* counting spin orders *)
DefConstantSymbol[SO];
DefConstantSymbol[SO1];
DefConstantSymbol[SO2];


HideSO[ex_] := ex/.{SO -> 1, SO1 -> 1, SO2 -> 1};
ShowSOSimple[e_] := HideSO[e]/.{
    S[X___] :> SO * S[X], Sv[X___] :> SO * Sv[X],
    Ssq[X__] :> SO^2 * Ssq[X],
    SPart[x_] :> SO * SPart[x], SSPart[x_] :> SO^2 * SSPart[x]
};
ShowSO[ex_] := ShowSOSimple[ex]/.{
    S[wl @ 1, i__] :> SO1 * S[wl @ 1, i], 
    S[wl @ 2, i__] :> SO2 * S[wl @ 2,i],
    Sv[wl @ 1, i__] :> SO1 * Sv[wl @ 1, i], 
    Sv[wl @ 2, i__] :> SO2 * Sv[wl @ 2, i],
    Ssq[wl @ 1,i__] :> SO1^2 * Ssq[wl @ 1, i],
    Ssq[wl @ 2, i__] :> SO2^2 * Ssq[wl @ 2, i]
};


PMPart[expr_] := (expr//ShowSO)/.{SO -> 0};
SOPart[expr_] := Coefficient[(expr//ShowSO)/.SO2 -> 0, SO1, 1];
SOPartF[expr_] := (
    Coefficient[(expr//ShowSO)/.SO2 -> 0, SO1, 1] 
    + Coefficient[(expr//ShowSO)/.SO1 -> 0, SO2, 1]
);
S1S2Part[expr_] := Coefficient[Coefficient[expr//ShowSO, SO1, 1], SO2, 1];
S1S1Part[expr_] := Coefficient[(expr//ShowSO)/.SO2 -> 0, SO1, 2];
S1S1PartF[expr_] := (
    Coefficient[(expr//ShowSO)/.SO2 -> 0, SO1, 2] 
    + Coefficient[(expr//ShowSO)/.SO1 -> 0, SO2, 2]
);
CutMass[ex_] := ex - (ex/.SO -> 0);


(* exchange of labels *)
ExChange[A_, B_][ex_] := ex/.{A -> B, B -> A};
Mirror[A_, B_][ex_] := ex + ExChange[A, B][ex];
Mirror12[ex_] := ex//Mirror[wl[1], wl[2]]//ShowSO;


(* PN power counting parameter *)
DefConstantSymbol[cInv, PrintAs -> "(\!\(\*SuperscriptBox[\(c\), \(-1\)]\))"];
(* cut at PN and/or spin order *)
$MaxPNOrder = 8;
$MaxSpinOrder = 2;
CutMore[o_][e_] := Series[e, {cInv, 0, $MaxPNOrder-o}]//Normal;
CutSpin[e_] := Series[e, {SO, 0, $MaxSpinOrder}]//Normal;
Cut4PN[ex_] := ex - cInv^8 * Coefficient[ex//PMPart, cInv, 8];
Cut3PN[ex_] := Cut4PN[ex] - cInv^6 * Coefficient[ex//PMPart, cInv, 6];
Cut[e_] := e//CutMore[0]//CutSpin//Cut3PN;


(* dimensional regulator d = 3 + \[Epsilon]d *)
DefConstantSymbol[\[Epsilon]d];
(* aux simplifications *)
SimpF[f_][e_] := Collect[e/.xRule/.mRule, {
    cInv, SO, SO1, SO2, accel, G, Scalar[r[__]], Scalar[m[__]], 
    Scalar[CES2[__]], \[Epsilon]d, Gamma[_], \[Pi]^_
    },
	ScreenDollarIndices @ f @ ToCanonical @ ContractMetric @ #&]/.xRule;
Simp[e_] := SimpF[PutScalar][e];
SimpNS[e_] := SimpF[NoScalar][e];
SimpFinal[e_] := Simp[e//ShowSO//ShowAccel];


(* convert sum of terms to list and vice versa *)
PlusToList[e_Plus] := List @@ e;
PlusToList[e_] := {e};
ListToPlus[l_List] := Plus @@ l;


(* put head on each term in a sum *)
PutHead[h_][e_] := ListToPlus[h /@ PlusToList @ Expand @ e];


(* apply transformation term by term, with optional status bar *)
TermByTerm[transfo_, bar_:False][e_] := Module[
    {terms, numterms, count = 0, result, time},
    terms = PlusToList @ e;
    numterms = Length[terms];
    If[bar,
        Print["Number of terms: ", numterms];
        Print[ProgressIndicator[Dynamic[count], {0, numterms}]];
    ];
    time = Timing[
        result = Plus @@ ((count++; transfo[#])& /@ terms);
    ] // First;
    If[bar, Print["Time: ", time, " s"];];
    result
];


(* timing *)
Needs["Units`"];
TimeIt[ex_] := Module[{time},
    time = First @ Timing[ex];
    timing == If[time < 60.0,
        Round[time, 0.1] * Second, 
        If[time < 60.0 * 60.0,
            Round[time / 60, 0.1] * Minute, 
            Round[time / 60 / 60, 0.1] * Hour 
        ] 
    ] 
];
SetAttributes[TimeIt, HoldFirst];


(* ::Subsection::Closed:: *)
(*save results, imports*)


SetDirectory[NotebookDirectory[]];


(* ::Subchapter::Closed:: *)
(*FeynRul*)


(* ::Subsection::Closed:: *)
(*definitions*)


(* fields. notice: 2nd label is time derivative *)
DefTensor[\[Phi][LI[], LI[]], {Md, t}];
DefTensor[A[LI[], LI[], i], {Md, t}];
DefTensor[\[Sigma][LI[], LI[], i, j], {Md, t}, Symmetric[{i, j}]];


(* Dirac delta of time points including time derivatives *)
DefTensor[\[Delta]t[LI[], LI[], LI[], LI[]], Md];


(* Fourier vectors *)
DefTensor[k[LI[], i], Const];
(* symbolic scalar representation *)
DefTensor[ks[LI[]], Const];


(* head for differential of integrals *)
DefInertHead[dd];


(* Exp including the I *)
DefScalarFunction[e];
Derivative[n_][e][x_] := I^n * e[x];


(* Dirac delta head *)
DefInertHead[D\[Delta]];


(* shorthand for delta of k vectors *)
\[Delta]k[A__] := D\[Delta] @ (Plus @@ (ks[pt @ #]& /@ {A}));


(* head for bare propagator *)
DefInertHead[prop];


(* ::Subsection::Closed:: *)
(*vertices manifold*)


DefManifold[Vertices, \[Infinity], {A1, A2, A3, A4, A5, A6, A7, A8, B1}];


(* propagators *)
DefTensor[\[Phi]\[Phi][LI[], LI[]], Vertices];
DefTensor[AA[LI[], LI[]], Vertices];
DefTensor[\[Sigma]\[Sigma][LI[], LI[]], Vertices];


(* propagator time insertions are treated as vertices *)
DefTensor[\[Phi]X\[Phi][LI[], LI[]], Vertices];
DefTensor[AXA[LI[], LI[]], Vertices];
DefTensor[\[Sigma]X\[Sigma][LI[], LI[]], Vertices];


(* bulk/field vertices *)
DefTensor[\[Phi]\[Phi]\[Phi][LI[], LI[], LI[]], Vertices];
DefTensor[\[Phi]\[Phi]A[LI[], LI[], LI[]], Vertices];
DefTensor[\[Phi]\[Phi]\[Sigma][LI[], LI[], LI[]], Vertices];
DefTensor[\[Phi]AA[LI[], LI[], LI[]], Vertices];
DefTensor[\[Phi]A\[Sigma][LI[], LI[], LI[]], Vertices];
DefTensor[AAA[LI[], LI[], LI[]], Vertices];
DefTensor[AA\[Sigma][LI[], LI[], LI[]], Vertices];
DefTensor[\[Phi]4[LI[], LI[], LI[], LI[]], Vertices];
DefTensor[\[Phi]\[Phi]AA[LI[], LI[], LI[], LI[]], Vertices];


(* worldline vertices *)
DefTensor[pk[LI[]], Vertices];
DefTensor[p\[Phi][LI[], LI[]], Vertices];
DefTensor[p\[Phi]\[Phi][LI[], LI[], LI[]], Vertices];
DefTensor[p\[Phi]3[LI[], LI[], LI[], LI[]], Vertices];
DefTensor[p\[Phi]4[LI[], LI[], LI[], LI[], LI[]], Vertices];
DefTensor[pA[LI[], LI[]], Vertices];
DefTensor[p\[Phi]A[LI[], LI[], LI[]], Vertices];
DefTensor[p\[Phi]\[Phi]A[LI[], LI[], LI[], LI[]], Vertices];
DefTensor[pAA[LI[], LI[], LI[]], Vertices];
DefTensor[p\[Sigma][LI[], LI[]], Vertices];
DefTensor[pA\[Sigma][LI[], LI[], LI[]], Vertices];
DefTensor[p\[Phi]\[Sigma][LI[], LI[], LI[]], Vertices];


(* ::Subsection::Closed:: *)
(*prepare rules*)


(* read Feynman rules from 2 output files, convert to current notation: 
   indices, fields, worldline dofs, constants, time derivatives *)
SimpFR[e_] := Collect[
    e, {cInv, SO, SO1, SO2, accel, Scalar[CES2[__]]}, Together
];
ImportRules[file_] := Get[file] /. {
    m -> m[wl[1]], CES2 -> CES2[wl[1]], v[i_] :> x[wl[1, 1], i], 
    a1[i_] :> x[wl[1, 2], i], S[i__] :> S[wl[1, 0], i],
    \[Phi][i___] :> \[Phi][pt[0, 0], i], A[i___] :> A[pt[0, 0], i],
    \[Sigma][i___] :> \[Sigma][pt[0, 0], i]
}/.MakeRule[{
    S[wl[1, 0], i, j] * S[wl[1, 0], -i, -j], 2 * Ssq[wl[1, 0]]
} // Evaluate]//.{
    ParamD[t, p___] @ T_[A___] :> ParamD[p] @ IncDt @ T[A]
}//ShowSOSimple//SimpFR//Simp;
frules = ImportRules["frules_field.dat.m"];
wlrules = ImportRules["frules_wl.dat.m"];


(* adjust PN count from Feynman rules files: 
   vertices are PNcounted only according to the matter dofs *)
AdjustPNCount[\[Phi]o_, Ao_, \[Sigma]o_][ex_] := ex / cInv^(0 * \[Phi]o + 1 * Ao + 2 * \[Sigma]o);


(* extract vertex with certain powers of the fields *)
DefConstantSymbol[Torder];
TensorCoeff[T_, o_][ex_] := Coefficient[
    ex/.T[i___] :> Torder * T[i], Torder, o
];
FieldCoeff[\[Phi]o_, Ao_, \[Sigma]o_][ex_] := (
    ex // TensorCoeff[\[Phi], \[Phi]o] // TensorCoeff[A, Ao] // TensorCoeff[\[Sigma], \[Sigma]o]
);


(* enumerate fields of the same type in a vertex using the point label *)
EnumerField[T_][ex_] := ListToPlus[Module[{count = 1}, #//.{
    T[pt[0], i___]^n_ :> T[pt[0], i]^(n - 1) * T[pt[count++], i],
    T[pt[0], i___] :> T[pt[count++], i]
}]& /@ PlusToList[Expand[NoScalar[ex]]]];
EnumerFields[ex_] := ex // EnumerField[\[Phi]] // EnumerField[A] // EnumerField[\[Sigma]];


(* permute same field in a vertex: summing all possible contractions of 
   the vertex. must be called after EnumerFields and before OffsetFields*)
PermuteRule[n_] := Thread[Range[n] -> #]& /@ Permutations[Range[n]];
PermuteField[T_, n_][ex_] := Plus @@ (ex/.{
    T[pt[p_], i___] :> T[pt[p/.#], i]
}& /@ PermuteRule[n]);
PermuteFields[\[Phi]o_, Ao_, \[Sigma]o_][ex_] := (
    ex // PermuteField[\[Phi], \[Phi]o] // PermuteField[A, Ao] // PermuteField[\[Sigma], \[Sigma]o]
);


(* offset label of fields of different type, so that every field has 
   a different label *)
OffsetFields[\[Phi]o_, Ao_, \[Sigma]o_][ex_] := ex/.{
    A[pt[nA_], i___] :> A[pt[nA + \[Phi]o], i], 
    \[Sigma][pt[nA_], i___] :> \[Sigma][pt[nA + \[Phi]o + Ao], i]
};


(* apply sequentially to collect all vertex contractions *)
VertexContractions[\[Phi]o_, Ao_, \[Sigma]o_][ex_] := (
    ex // EnumerFields // PermuteFields[\[Phi]o, Ao, \[Sigma]o] // OffsetFields[\[Phi]o, Ao, \[Sigma]o]
);


(* prefactors for each field in vertex *)
FieldFactors[\[Phi]o_, Ao_, \[Sigma]o_][ex_] := ex * Module[{P}, Product[
    dd[ks[pt @ P]] * \[Delta]t[pt[P, 0], pt[0, 0]], {P, \[Phi]o + Ao + \[Sigma]o}
]];


(* Fourier spatial derivatives. Call after VertexContractions *)
FourierCD[ex_] := ex//.{
    CD[i_] @ T_[pt[A_, n_], j___] :> I * k[pt @ A, i] * T[pt[A, n], j],
    CD[j_] @ k[A_, i_] -> 0
};


(* flip time derivatives from fields to \[Delta]t. 
   Call after FieldFactors and FourierCD *)
FlipDt[ex_] := (ex // Simp // NoScalar)//.{
    \[Delta]t[X___, pt[A_, nA_], Y___] * T_[pt[A_, n_?Positive], i___] :> (
        -\[Delta]t[X, pt[A, nA + 1], Y] * T[pt[A, n - 1], i]
    )
} // ScreenDollarIndices;


(* put all together: generic vertex preparation *)
PrepareVertex[\[Phi]o_, Ao_, \[Sigma]o_][ex_] := (
    ex//FieldCoeff[\[Phi]o, Ao, \[Sigma]o]//AdjustPNCount[\[Phi]o,Ao,\[Sigma]o]
    //VertexContractions[\[Phi]o, Ao, \[Sigma]o]//FourierCD//FieldFactors[\[Phi]o, Ao, \[Sigma]o]
    //FlipDt//SimpNS
);
(* replace points to names in LHS of vertexRules, see below *)
ReplacePoints[ex_] := ex/.{
    pt[1] -> pt[A1], pt[2] -> pt[A2], pt[3] -> pt[A3], pt[4] -> pt[A4]
};
(* special preparation of worldline vertex: 
   e-factors and replace bulk point by worldline point *)
WlVertex[\[Phi]o_, Ao_, \[Sigma]o_] := Module[
    {P, j}, 
    Product[e[k[pt @ P, j] * x[wl[B1, 0], -j]], {P, \[Phi]o + Ao + \[Sigma]o}]
        * PrepareVertex[\[Phi]o, Ao, \[Sigma]o][wlrules] /. {
            pt[0] -> wl[B1], wl[1] -> wl[B1]
        }//ReplacePoints
];
(* special preparation of bulk/field vertex: momentum conservation *)
BlVertex[\[Phi]o_, Ao_, \[Sigma]o_] := Module[
    {P}, D\[Delta] @ Sum[ks[pt @ P], {P, \[Phi]o + Ao + \[Sigma]o}]
        * PrepareVertex[\[Phi]o, Ao, \[Sigma]o][frules]//ReplacePoints
];
(* prepare end vertex so that time derivatives drop on it *)
EndVertex[ex_] := ex//.{
    \[Delta]t[wl[A_, nA_], pt[B_, nB_?Positive]] :> (
        (-1)^nB * \[Delta]t[wl[A, nA + nB], pt[B, 0]]
    ),
    \[Delta]t[pt[B_, nB_?Positive], wl[A_, nA_]] :> (
        (-1)^nB * \[Delta]t[pt[B, 0], wl[A, nA + nB]]
    )
};


(* ::Subsection::Closed:: *)
(*propagators*)


dtld = d - 2;
cd = 2 * (d - 1) / dtld;


P[i_, j_, k_, l_] := 1/2 * (
	delta[i, k] * delta[j, l] + delta[i, l] * delta[j, k] 
    + Together[2 - cd] * delta[i, j] * delta[k, l]
);


propagatorRules = {
    \[Phi]\[Phi][pt @ A1_, pt @ A2_] * \[Phi][pt[A1_, 0]] * \[Phi][pt[A2_, 0]] :> 
    4 / cd * 4\[Pi] G
        * \[Delta]k[A1, A2] * \[Delta]t[pt[A1, 0], pt[A2, 0]] * prop[(ks @ pt @ A1)^2]
    ,
    AA[pt @ A1_, pt @ A2_] * A[pt[A1_, 0], i_] * A[pt[A2_, 0], j_] :> 
    -16\[Pi] G * delta[i, j]
        * \[Delta]k[A1, A2] * \[Delta]t[pt[A1, 0], pt[A2, 0]] * prop[(ks @ pt @ A1)^2]
    ,
    \[Sigma]\[Sigma][pt @ A1_, pt @ A2_]
        * \[Sigma][pt[A1_, 0], i1_, i2_] * \[Sigma][pt[A2_, 0] ,j1_ ,j2_]
    :> 
    32\[Pi] G * P[i1, i2, j1, j2]
        * \[Delta]k[A1, A2] * \[Delta]t[pt[A1, 0], pt[A2, 0]] * prop[(ks @ pt @ A1)^2]
};


(* ::Subsection::Closed:: *)
(*vertices*)


vertexRules = {
    (* propagator insertions treated as bulk vertices *)
    \[Phi]X\[Phi][pt @ A1_, pt @ A2_] :> 
    cd /4 2 * cInv^2 / (8\[Pi] G) * dd[ks @ pt @ A1] * dd[ks @ pt @ A2]
        * \[Delta]k[A1, A2] * \[Delta]t[pt[A1, 1], pt[A2, 1]]
        * \[Phi][pt[A1, 0]] * \[Phi][pt[A2, 0]]
    ,
    AXA[pt @ A1_, pt @ A2_] :> 
    -2 * cInv^2 / (32\[Pi] G) * dd[ks @ pt @ A1] * dd[ks @ pt @ A2]
        * \[Delta]k[A1, A2] * \[Delta]t[pt[A1, 1], pt[A2, 1]] * Module[{i}, 
            A[pt[A1, 0], i] * A[pt[A2, 0], -i]
        ]
    ,
    \[Sigma]X\[Sigma][pt @ A1_, pt @ A2_] :> 
    2 * cInv^2 / (128\[Pi] G) * dd[ks @ pt @ A1] * dd[ks @ pt @ A2]
        * \[Delta]k[A1, A2] * \[Delta]t[pt[A1, 1], pt[A2, 1]] * Module[{i, j}, 
            2\[Sigma][pt[A1, 0], i, j] * \[Sigma][pt[A2, 0], -i, -j] 
            - \[Sigma][pt[A1, 0], i, -i] * \[Sigma][pt[A2, 0], j, -j]
        ]
    ,
    (* field vertices *)
    \[Phi]\[Phi]\[Phi][pt @ A1_, pt @ A2_ , pt @ A3_] -> BlVertex[3, 0, 0],
    \[Phi]\[Phi]A[pt @ A1_, pt @ A2_, pt @ A3_] -> BlVertex[2, 1, 0],
    \[Phi]\[Phi]\[Sigma][pt @ A1_, pt @ A2_, pt @ A3_] -> BlVertex[2, 0, 1],
    \[Phi]AA[pt @ A1_, pt @ A2_, pt @ A3_] -> BlVertex[1, 2, 0],
    \[Phi]A\[Sigma][pt @ A1_, pt @ A2_, pt @ A3_] -> BlVertex[1, 1, 1],
    AAA[pt @ A1_, pt @ A2_, pt @ A3_] -> BlVertex[0, 3, 0],
    AA\[Sigma][pt @ A1_, pt @ A2_, pt @ A3_] -> BlVertex[0, 2, 1],
    \[Phi]4[pt @ A1_, pt @ A2_, pt @ A3_, pt @ A4_] -> BlVertex[4, 0, 0],
    \[Phi]\[Phi]AA[pt @ A1_, pt @ A2_, pt @ A3_, pt @ A4_] -> BlVertex[2, 2, 0],
    (* worldline vertices *)
    pk[wl @ B1_] -> WlVertex[0, 0, 0],
    p\[Phi][wl @ B1_, pt @ A1_] -> EndVertex @ WlVertex[1, 0, 0],
    p\[Phi]\[Phi][wl @ B1_, pt @ A1_, pt @ A2_] -> WlVertex[2, 0, 0],
    p\[Phi]3[wl @ B1_, pt @ A1_, pt @ A2_, pt @ A3_] -> WlVertex[3, 0, 0],
    p\[Phi]4[wl @ B1_, pt @ A1_, pt @ A2_, pt @ A3_, pt @ A4_] -> (
        WlVertex[4, 0, 0]
    ),
    pA[wl @ B1_, pt @ A1_] -> EndVertex @ WlVertex[0, 1, 0],
    p\[Phi]A[wl @ B1_, pt @ A1_, pt @ A2_] -> WlVertex[1, 1, 0],
    p\[Phi]\[Phi]A[wl @ B1_, pt @ A1_, pt @ A2_, pt @ A3_] -> WlVertex[2, 1, 0],
    pAA[wl @ B1_, pt @ A1_, pt @ A2_] -> WlVertex[0, 2, 0],
    p\[Sigma][wl @ B1_, pt @ A1_] -> EndVertex @ WlVertex[0, 0, 1],
    p\[Phi]\[Sigma][wl @ B1_, pt @ A1_, pt @ A2_] -> WlVertex[1, 0, 1],
    pA\[Sigma][wl @ B1_, pt @ A1_, pt @ A2_] -> WlVertex[ 0, 1, 1]
}/.{
    (L_ -> R_) :> (L :> ReplaceDummies[R/.{pt @ 0 -> pt @ Unique[]}])
};


(* cut worldline vertex according to spin order *)
SpinProjectorList = {mPart, SPart, SSPart};
DefInertHead /@ SpinProjectorList;
partRules = {
    mPart[ex_] :> (ex/.SO -> 0),
    SPart[ex_] :> Coefficient[ex, SO, 1],
    SSPart[ex_] :> Coefficient[ex, SO, 2]
};
SpinProjectorQ[sym_] := MemberQ[SpinProjectorList, sym];


(* ::Subchapter::Closed:: *)
(*FeynGen*)


(* ::Subsection::Closed:: *)
(*import generated Feynman diagrams*)


(* import Feynman diagrams *)
FDiagrams = Get["PNdiagrams.dat.m"] // Cut3PN // Expand;


(* ::Subsection::Closed:: *)
(*convert diagrams*)


GlueWorldlines[expr_] := expr/.{
    Wl1F[LI_, i_, inds___] :> Glue1[wl @ i] * Wl1F[LI, i, inds],
    Wl2F[LI_, i_, inds___] :> Glue2[wl @ i] * Wl1F[LI, i, inds]
}/.{
    proj_?SpinProjectorQ[Glue1[A_] * v_] :> Glue1[A] * proj @ v,
    proj_?SpinProjectorQ[Glue2[A_] * v_] :> Glue2[A] * proj @ v
}//.{
    Glue1[A__] * Glue1[B__] :> Glue1[A, B],
    Glue2[A__] * Glue2[B__] :> Glue2[A, B]
} /.{
    Glue1[A__] :> Glue[wl @ 1, A],
    Glue2[A__] :> Glue[wl @ 2, A]
};


WlVertexQ[v_] := MemberQ[{Wl1F, Wl2F}, v];


ConvertDiagrams[expr_] := GlueWorldlines[expr]/.{
    (* propagators *)
    Prop\[Phi][inds__] :> \[Phi]\[Phi] @@ pt /@ (-{inds}),
    PropA[inds__] :> AA @@ pt /@ (-{inds}),
    Prop\[Sigma][inds__] :> \[Sigma]\[Sigma] @@ pt /@ (-{inds}),
    (* propagator insertions *)
    VertexF[LI[2, 0, 0], inds__] :> \[Phi]X\[Phi] @@ pt /@ {inds},
    VertexF[LI[0, 2, 0], inds__] :> AXA @@ pt /@ {inds},
    VertexF[LI[0, 0, 2], inds__] :> \[Sigma]X\[Sigma] @@ pt /@ {inds},
    (* field vertices *)
    VertexF[LI[3, 0, 0], inds__] :> \[Phi]\[Phi]\[Phi] @@ pt /@ {inds},
    VertexF[LI[2, 1, 0], inds__] :> \[Phi]\[Phi]A @@ pt /@ {inds},
    VertexF[LI[2, 0, 1], inds__] :> \[Phi]\[Phi]\[Sigma] @@ pt /@ {inds},
    VertexF[LI[1, 2, 0], inds__] :> \[Phi]AA @@ pt /@ {inds},
    VertexF[LI[1, 1, 1], inds__] :> \[Phi]A\[Sigma] @@ pt /@ {inds},
    VertexF[LI[0, 3, 0], inds__] :> AAA @@ pt /@ {inds},
    VertexF[LI[0, 2, 1], inds__] :> AA\[Sigma] @@ pt /@ {inds},
    VertexF[LI[4, 0, 0], inds__] :> \[Phi]4 @@ pt /@ {inds},
    VertexF[LI[2, 2, 0], inds__] :> \[Phi]\[Phi]AA @@ pt /@ {inds},
    (* worldline vertices *)
    wlF_?WlVertexQ[LI[1, 0, 0], i_, inds___] :> p\[Phi][
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[2, 0, 0], i_, inds___] :> p\[Phi]\[Phi][ 
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[3, 0, 0], i_, inds___] :> p\[Phi]3[
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[4, 0, 0], i_, inds___] :> p\[Phi]4[
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[0, 1, 0], i_, inds___] :> pA[
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[1, 1, 0], i_, inds___] :> p\[Phi]A[
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[2, 1, 0], i_, inds___] :> p\[Phi]\[Phi]A[
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[0, 2, 0], i_, inds___] :> pAA[
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[0, 0, 1], i_, inds___] :> p\[Sigma][
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[1, 0, 1], i_, inds___] :> p\[Phi]\[Sigma][
        wl @ i, Sequence @@ pt /@ {i, inds}
    ],
    wlF_?WlVertexQ[LI[0, 1, 1], i_, inds___] :> pA\[Sigma][
        wl @ i, Sequence @@ pt /@ {i, inds}
    ]
}/.{cInv -> 1, G -> 1, SO -> 1};


(* ::Subsection::Closed:: *)
(*generate PN graphs*)


PropList = {Prop\[Phi], PropA, Prop\[Sigma]};
PropagatorQ[s_] := MemberQ[PropList, s];


(* generate graph corresponding to PN contraction *)
MakePNGraphTerm[expr_] := Module[
	{
	    pstyle, vstyle, insertion, Slin, Ssquare, 
        ex, wl1, wl2, v, properties
	},
	pstyle[Prop\[Phi]] = Red;
	pstyle[PropA] = {Dashed, Darker[Green]};
	pstyle[Prop\[Sigma]] = {Thickness[.02], Blue};
	vstyle[insertion] = {
        VertexSize -> 0.1, VertexShapeFunction -> "Star"
    };
	vstyle[Slin] = {
        VertexSize -> 0.2, VertexShapeFunction -> "Capsule"
    };
	vstyle[Ssquare] = {
        VertexSize -> 0.2, VertexShapeFunction -> "Square"
    };
    (* adding ``past'' tip points to the worldlines *)
	ex = expr * wl1[Unique[]] * wl2[Unique[]]  /. { 
        mPart -> Identity 
        } /. {
		SPart @ Wl1F[LI[___], inds___] :> (
            v[Unique[], Slin, wl1][inds]
        ),
		SPart @ Wl2F[LI[___], inds___] :> (
            v[Unique[], Slin, wl2][inds]
        ),
		SSPart @ Wl1F[LI[___], inds___] :> (
            v[Unique[], Ssquare, wl1][inds]
        ),
		SSPart @ Wl2F[LI[___], inds___] :> (
            v[Unique[], Ssquare, wl2][inds]
        ),
		Wl1F[LI[___], inds___] :> v[Unique[], wl1][inds],
		Wl2F[LI[___], inds___] :> v[Unique[], wl2][inds],
        VertexF[LI[___], i1_, i2_] :> v[Unique[], insertion][i1, i2],
		VertexF[LI[___], inds___] :> v[Unique[]][inds]
	} //. {
		wl1[i___] * v[tg_, type___, wl1][j___] :> (
            wl1[i, tg] * v[tg, type][j]
        ),
		wl2[i___] * v[tg_, type___, wl2][j___] :> ( 
            wl2[i, tg] * v[tg, type][j]
        )
	} /. {(* adding ``future'' tip points to the worldlines *) 
        wl1[i__] :> wl1[{i, Unique[]}], wl2[i__] :> wl2[{i, Unique[]}]
    };
	properties = Reap[ex /. { 
        v[tg_, type_] :> Sow[Property[tg, vstyle[type]]] 
    }]  //  Last  //  Flatten;
	ex = Reap[ex /. { v[tg_, type_] :> v[tg] } //. {
		wl1[l_List] :> Times @@ (Sow /@ Table[Style[
            UndirectedEdge[l[[i]], l[[i + 1]]], {Thickness[.015], Black}
        ],
        {i, 1, Length[l] - 1}
        ]),
		wl2[l_List] :> Times @@ (Sow /@ Table[
            Style[UndirectedEdge[l[[i]], l[[i + 1]]], {Thick, Black}],
            {i, 1, Length[l] - 1}
        ]),
        v[tg1___][i1___, A1_, i2___] * p_?PropagatorQ[-A1_, -A2_]
            * v[tg2___][i3___, A2_, i4___]
        :> 
        Sow[Style[UndirectedEdge[tg1, tg2], pstyle[p]]]
            * v[tg1][i1, i2] * v[tg2][i3, i4]
	}];
	{ex[[1]] /. { 
        v[___][___] -> 1, UndirectedEdge[___] -> 1, Style[___] -> 1 
    },
	Graph[properties, ex[[2, 1]]] 
    }
];


(* generate graphs corresponding to sum of PN contractions *)
MakePNGraphs[expr_] := MakePNGraphTerm /@ PlusToList[
    expr //  Expand // NoScalar
];


(* ::Subchapter::Closed:: *)
(*FeynInteg*)


(* ::Subsection::Closed:: *)
(*time derivative*)


(* similar to xTensor *)
dt[A_][sum_Plus] := Map[dt[A], sum];
dt[A_][x_ * y_] := dt[A][x] * y + x * dt[A][y];
MultiD[der_, f_[args__]] := (
    Derivative[Sequence @@ #][f][args]& /@ IdentityMatrix[Length[{args}]]
    ) . (der /@ ReplaceDummies /@ {args});
dt[A_][f_?ScalarFunctionQ[args___]] := MultiD[dt[A], f[args]];
dt[A_][Scalar[expr_]] := dt[A][ReplaceDummies[expr]];
dt[A_][_?ConstantQ] = 0;


(* additional rules *)
dt[A_][H_?InertHeadQ[args___]] := MultiD[dt[A], H[args]];
dt[A_][_?ConstTensorQ[___]] = 0;
dt[A_][_?xTensorQ[B___]] /; FreeQ[{B}, A] := 0;


(* flip dt on \[Delta]t for partial integrations. 
   must be applied before the main rule *)
dt[p @ A_][\[Delta]t[X___, pdt[A_, n_], Y___]] := (
    -\[Delta]t[pdt[A, n], AddDt[1][X, Y]]
);


(* main rule: increases time derivative label *)
dt[p @ A_][T_[pdt[A_, n_], i___]] := T[pdt[A, n + 1], i];


(* n-times time derivative *)
Dtn[A_, n_][ex_] := Nest[dt[A], ex, n];


(* define time derivatives of r and xRel. 
   not needed for integration, but needed for total time derivatives 
   in comparisons*)
dt[A_][xRel[A_, B_, i_]] := x[A, td[1], i];
dt[B_][xRel[A_, B_, i_]] := -x[B, td[1], i];
dt[A_][r[A_, B_]] := Scalar[xRel[A, B, i] * x[A, td[1], -i]] / r[A, B];
dt[B_][r[A_, B_]] := Scalar[xRel[B, A, i] * x[B, td[1], -i]] / r[A, B];
(* total time derivative with respect to "both" worldline times *)
Dt12[ex_] := dt[wl @ 1][ex] + dt[wl @ 2][ex];


(* ::Subsection::Closed:: *)
(*time integrations*)


(* head for time integration: useful for formulating partial integration *)
DefInertHead[IntT, LinearQ -> True];
IntT[0] = 0;


(* flip time derivatives on \[Delta]t until they reach endpoints on a worldline *)
FlipOn\[Delta]t[ex_] := ex//.{
    IntT[\[Delta]t[X1___, pdt[A_, n1_?Positive], Y1___]
        * \[Delta]t[X2___, pdt[A_, n2_], Y2___] * e_
	]
    :> 
    PutHead[IntT][(-1)^n1 * \[Delta]t[X1, pdt[A, 0], Y1]
        * Dtn[p @ A, n1][\[Delta]t[X2, pdt[A, n2], Y2] * e]
    ]
};


(* partial integration at endpoints *)
PartialIntEndpoints[ex_] := ex//.{
    IntT[\[Delta]t[X___, wl[A_, n_?Positive], Y___] * e_] :> 
    PutHead[IntT][(-1)^n * \[Delta]t[X, wl[A, 0], Y] * Dtn[wl @ A, n] @ e]
};


(* symbol to glue worldline points: defined by "RemoveIntT" below *)
DefTensor[Glue[LI[], LI[]], Const];
SetAttributes[Glue, Orderless];
(* remove product of \[Delta]t, glue worldline points to worldline, 
   remove IntT head *)
RemoveIntT[ex_] := ex/.{
    \[Delta]t[pdt[_, 0], pdt[_, 0]] -> 1
}/.{\[Delta]t[X___] :> ERROR[" IntT failed "\[Delta]t[X]]}//.{
    IntT[Glue[wl_, pts__] * e_] :> IntT[e/.(# -> wl& /@ {pts})]
}/.{IntT -> Identity};


(* main function for time integrations *)
Integrate\[Delta]t[e_] := (
    PutHead[IntT][e] // FlipOn\[Delta]t // PartialIntEndpoints // RemoveIntT
);


(* ::Subsection::Closed:: *)
(*integration over Dirac deltas of momenta*)


(* head for integrals *)
DefInertHead[Int, LinearQ -> True];


(* simplify and order propagators *)
SimpProp[e_] := e/.prop[ex_] :> prop[ex // Simplify]/.{
    dd[ks @ A_] * prop[(X__ - ks @ A_)^2] :> (
        dd[ks @ A] * prop[(ks @ A - Plus[X])^2]
    )
};
(* expand integrals *)
ExpandInt[ex_] := ex/.{
    Int[e_] :> Int @ ContractMetric @ Expand @ ExpandInt @ e
}//.{
    Int[Verbatim[Times][L___, T_, R___]] /; 
    And[FreeQ[T, ks], FreeQ[T, k]] :> T * Int[L * R],
    Int[e_] /; Or[FreeQ[e, dd], And[FreeQ[e, ks], FreeQ[e, k]]] :> e,
    Int[] -> 1
} // SimpProp;
(* head on terms in int *)
PrepareIntegrals[ex_] := PutHead[Int][ex] // ExpandInt;


(* integrate over Dirac deltas *)
IntD\[Delta][e_, modF_:Identity] := e//.{
    Int[dd[X_] * D\[Delta][s_] * ex_] /; MemberQ[s, X, \[Infinity]] :> Int[
        ex/Abs[D[s, X]]/.modF[First[Solve[s == 0, X]]]
    ]
};
(* specialize to integrals involving \[Delta]k *)
ksTok[{A_ -> B_}] := {(A/.ks -> (k[#, i_]&)) -> (B/.ks -> (k[#, i]&))};
Integrate\[Delta]k[ex_] := IntD\[Delta][PrepareIntegrals[ex], (Join[#, ksTok[#]])&];


(* ::Subsection::Closed:: *)
(*factorizing integrals*)


(* integral of single variable, used in intermediate transformations *)
DefInertHead[Int1, LinearQ -> True];


(* pull independent variables out of the integral *)
ExpelIndep[ex_] := ex//.{
    Int1[Verbatim[Times][L___, T_, R___], dd[ks @ A_]]/;
    And[FreeQ[T, ks @ A], FreeQ[T, k[A, ___]]] :> (
        T * Int1[L*R, dd[ks @ A]]
    )
};
RemoveInt1[ex_] := ex//. Int1[i_, x_] :> Int[x * i];
(* convert to integral over single variables *)
ToSingleInt[ex_] := ex//.{
    Int[dd[ks @ A_] * e_] :> Int[Int1[e, dd[ks @ A]] // ExpelIndep]
}/.Int->Identity // RemoveInt1;
(* to multiple int *)
ToMultiInt[ex_] := ex//.{Int[e1_ * Int[e2_]] :> Int[e1 * e2]};


(* try to factorize integrals by converting to single integrations and back *)
TryFactorInt[ex_] := ex // ToSingleInt // ToMultiInt;
FactorIntegrals[ex_] := ex//.{
    Int[dd[ks @ A_] * dd[ks @ B_] * e_] :> (
        TryFactorInt @ Int[dd[ks @ A] * dd[ks @ B] * e]
    )
};


(* ::Subsection::Closed:: *)
(*changing integration variables*)


(* change of integration variable *)
ChangeIntVRule[ksN_][ksRule_] := Join[
    ksRule/.{(L_ -> R_) :> (dd[L] -> Abs[D[R/.ksRule, ksN]]*dd[ksN])},
    ksTok[ksRule], ksRule
];
ChangeIntVar[ex_, P_, v_] := Module[{Pn = pt @ Unique[]},
    ex/.ChangeIntVRule[ks @ Pn] @ First @ Solve[v == ks @ Pn, ks @ P]
     // ExpandInt
];


(* simplify exponents *)
SimpExp[ex_] := ex//.{Int[e1_ * Int[e2_]] :> Int[e1 * e2]}//.{
    e[X_] * e[Y_] :> e[Collect[
        (X + Y // NoScalar // ToCanonical // Simplify // ScreenDollarIndices)
        /.xRule, xRel[__]
    ] // Scalar]
};
(* change integration variable to Fourier k *)
ChangeIntVToFourierk[expr_] := SimpExp[expr]/.{
    Int[dd[ks @ pt @n_] * e @ Scalar[kk_ * xRel[X__]] * ex___]/;
    MemberQ[kk, k[pt @ n, _], \[Infinity]] :> 
    ChangeIntVar[
        Int[dd[ks @ pt @ n] * e @ Scalar[kk * xRel[X]] * ex], pt @ n, 
        kk/.{k[pt @ l_, _] :> ks[pt @ l]}
    ],
    Int[dd[ks @ pt @ n_] * e[-Scalar[kk_ * xRel[X__]]] * ex___]/;
    MemberQ[{kk}, k[pt @ n, _], \[Infinity]] :> 
    ChangeIntVar[
        Int[dd[ks @ pt @ n] * e[-Scalar[kk * xRel[X]]] * ex], pt @ n,
        -kk/.{k[pt @ l_, _] :> ks[pt @ l]}
    ]
};


(* variable changes needed for nesting integrals *)
NestChangeVar[ex_] := ex//.{
    Int[dd[ks @ A_]
        * prop[(ks @ A_ + X_)^2] * prop[(ks @ A_ + X_ + Y__)^2] * e_
    ] :> 
    ChangeIntVar[Int[dd[ks @ A]
        * prop[(ks @ A + X)^2] * prop[(ks @ A + X + Y)^2] * e
    ], A, ks @ A + X]
};
OneLoopChangeVar[ex_] := SimpProp[ex]//.{
    Int[dd[ks @ A_]
        * prop[(ks @ A_ + X_)^2] * prop[(ks @ A_ + Y_)^2] * kk_
    ] :> 
    ChangeIntVar[Int[dd[ks @ A]
        * prop[(ks @ A + X)^2] * prop[(ks @ A + Y)^2] * kk
    ], A, ks @ A + X]
};


(* ::Subsection::Closed:: *)
(*nesting integrals*)


(* check for propagators with certain k *)
NoPropWith[A_][e_] := FreeQ[Reap[e/.prop -> Sow], ks @ A];
(* nest loop intergrals *)
NestLoops[ex_] := NestChangeVar[ex]//.{
    Int[dd[ks @ A_] * dd[ks @ B_] * prop[p1_] * prop[p2_] * e_]/; And[
        MemberQ[p1, ks @ A, \[Infinity]], MemberQ[p2, ks @ A, \[Infinity]], NoPropWith[A][e]
    ] :> Int[dd[ks @ B](
        Int1[prop[p1] * prop[p2] * e, dd[ks @ A]]
         // ExpelIndep // RemoveInt1 // OneLoopChangeVar
    )]
};


(* nest first integral with exp *)
NestExp[ex_] := ex/.{
    Int[dd[ks @ A_] * dd[B_] * e[E_] * expr_]/; MemberQ[E, k[A, _], \[Infinity]] :> 
    Int[dd[ks @ A] * e[E] * NestLoops @ TryFactorInt @ Int[dd[B] * expr]]
};


(* try to nest integrals *)
NestIntegrals[ex_] := ExpandInt[ex // ChangeIntVToFourierk]//.{
    Int[dd[ks @ A_] * dd[ks @ B_] * e_] :> (
        Int[dd[ks @ A] * dd[ks @ B] * e] // NestExp // NestLoops // SimpProp
    )
};


(* ::Subsection::Closed:: *)
(*import master integrals*)


(* read master integrals from "NLoop" output file *)
masterIntegrals = Get["MasterIntegrals.dat.m"] // Dispatch;
(* masterJrules appears on right hand side of masterIntegrals 
   through masterJshift in NLoop *)
masterJrules = Get["masterJrules.dat.m"] // Dispatch;
InsertMaster[ex_] := ExpandInt[ex/.masterIntegrals];


(* ::Subsection::Closed:: *)
(*main*)


FeynIntegrate[ex_] := FixedPoint[
    (# // FactorIntegrals // NestIntegrals // InsertMaster)&, ex
];
(* insert Feynman rules *)
InsertFRules[ex_] := Expand[
    ex/.vertexRules/.partRules // NoScalar // Cut // ScreenDollarIndices
]//.propagatorRules;
(* take limit in dimension *)
DimLimit[ex_] := Simp[ex] // Expand // TermByTerm[
     Simp @ (PowerExpand[#, {}]&) @ FunctionExpand @ Normal @ Series[
         #/.d -> 3 + \[Epsilon]d, {\[Epsilon]d, 0, 0}
     ]&,True
];
(* main integration fuction *)
JustIntegrate[ex_] := (
    ex // InsertFRules // Integrate\[Delta]t // Integrate\[Delta]k // FeynIntegrate // DimLimit
);
IntegrateF[ex_] := ex // JustIntegrate // SimpFinal;
IntegrateMirror[ex_] := ex // JustIntegrate // Mirror12 // SimpFinal;


(* automatic integration *)
IntegrateAutoTerm[ex_] := ( 
    Print[MakePNGraphTerm[ex]];
    {ex, ex // ConvertDiagrams // IntegrateF}
);
IntegrateAuto[ex_] := IntegrateAutoTerm /@ PlusToList @ Expand @ ex;
SumDiagrams[l_List] := Plus @@ Last @ Transpose @ l;


(* ::Subchapter::Closed:: *)
(*INTERRUPT*)


Interrupt[];


(* ::Subchapter::Closed:: *)
(*FeynComp*)


(* ::Subsection::Closed:: *)
(*example: 2PN point mass - simplest 2-loop sector*)


(* G^0 kinematic contributions to the effective action *)
LEFTkin = WlVertex[0, 0, 0]/.B1 -> 1 // Mirror12 // Cut;


(* integrate all diagrams *)
L2PNdiagrams = Coefficient[FDiagrams, SO, 0]//IntegrateAuto; // TimeIt


(* complete effective action/Lagrangian *)
L2PN = LEFTkin + SumDiagrams @ L2PNdiagrams // SimpFinal;


(* compare with previous result *)
L2PN - Get[FileNameJoin[{"results", "LEFT.dat.m"}]] // PMPart // SimpFinal


(* ::Subsection::Closed:: *)
(*automatic computation up to NNLO quadratic in spin*)


(* remove few "slow" diagrams, computed manually below *)
manualNums = Range[243,249];
automaticDiagrams = Fold[Delete, FDiagrams, Sort[manualNums, Greater]];


(* show number of diagrams to compute automatically *)
automaticDiagrams // Length


(* ::Text:: *)
(*NOTE: before running this, switch "Print[] command output" to *)
(*"Print to Console" in Edit->Preferences->Messages, *)
(*to have all the output messages in a separate window*)


(* integrate over all the above diagrams; total timing circa 3.5 days *)
integratedDiagrams = automaticDiagrams//IntegrateAuto;//TimeIt


(* save result *)
Put[integratedDiagrams, FileNameJoin[{"results", "integratedDiagrams.dat.m"}]];


(* ::Subsection::Closed:: *)
(*``manual'' computation of remaining diagrams*)


(* show remaining diagrams *)
manualDiagrams = ListToPlus @ (FDiagrams[[#]]& /@ manualNums);
manualDiagrams // MakePNGraphs


(* slow: timing circa 25hrs, inserting contraction manually *)
manualDiagram1 = (
    pA[wl @ 1, pt @ 11] * AA[pt @ 11, pt @ 1]
    * p\[Phi][wl @ 2, pt @ 21] * \[Phi]\[Phi][pt @ 21, pt @ 2]
    * Glue[wl @ 1, wl @ 3] * p\[Phi][wl @ 3, pt @ 31] * \[Phi]\[Phi][pt @ 31, pt @ 3]
    * Glue[wl @ 2, wl @ 4] * pA[wl @ 4, pt @ 41] * AA[pt @ 41, pt @ 4]
    * \[Phi]AA[pt @ 2, pt @1, pt @ 5] * AA[pt @ 5, pt @ 6]
    * \[Phi]AA[pt @ 3, pt @ 4, pt @ 6]
)//IntegrateF;//TimeIt


(* save result *)
Put[manualDiagram1, FileNameJoin[{"results", "manualDiagram1.dat.m"}]];


(* very slow: timing circa 11hrs, inserting contraction manually *)
manualDiagram2 = (
	1/2 * pA[wl @ 1, pt @ 11] * AA[pt @ 11, pt @ 1]
    * p\[Phi][wl @ 2, pt @ 21] * \[Phi]\[Phi][pt @ 21, pt @ 2]
    * Glue[wl @ 1, wl @ 3] * pA[wl @ 3, pt @ 31] * AA[pt @ 31, pt @ 3]
    * Glue[wl @ 2, wl @ 4] * p\[Phi][wl @ 4, pt @ 41] * \[Phi]\[Phi][pt @ 41, pt @ 4]
    * \[Phi]AA[pt @ 2, pt @ 1, pt @ 5] * AA[pt @ 5, pt @ 6]
    * \[Phi]AA[pt @ 4, pt @ 3, pt @ 6]
)//IntegrateMirror;//TimeIt


(* save result *)
Put[manualDiagram2, FileNameJoin[{"results", "manualDiagram2.dat.m"}]];


(* ::Subsection::Closed:: *)
(*sum effective action*)


(* get G^0 kinematic contributions to the effective action *)
LEFTkin = WlVertex[0, 0, 0]/.B1 -> 1 // Mirror12 // Cut;


(* sum interaction part of the effective action *)
integratedDiagrams = Get[
    FileNameJoin[{"results", "integratedDiagrams.dat.m"}]
];
manualDiagram1 = Get[FileNameJoin[{"results", "manualDiagram1.dat.m"}]];
manualDiagram2 = Get[FileNameJoin[{"results", "manualDiagram2.dat.m"}]];
LEFTauto = SumDiagrams @ integratedDiagrams;
LEFTint = LEFTauto + manualDiagram1 + manualDiagram2;


(* sum total effective action/Lagrangian *)
LEFT = LEFTkin + LEFTint // SimpFinal;


(* compare with previous result *)
LEFT - Get[FileNameJoin[{"results", "LEFT.dat.m"}]] // SimpFinal


(* optional: save result *)
(* Put[LEFT,FileNameJoin[{"results","LEFT.dat.m"}]]; *)
