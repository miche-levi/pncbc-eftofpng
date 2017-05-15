(* ::Package:: *)

(* ::Title:: *)
(*Package EFTofPNG version 0.99*)


(* ::Chapter:: *)
(*EFTofPNG: Feynman rules*)


(* ::Section::Closed:: *)
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


(* ::Section::Closed:: *)
(*xTensor setup*)


(* load xTensor package *)
Needs["xAct`xTensor`"];
(* generic number of spatial dimensions *)
DefConstantSymbol[d];
(* flat background spatial manifold *)
DefManifold[Mflat, d, {i, j, l, i1, i2, i3, i4}];
(* useful dimensional constants *)
dtld = d - 2;
cd = 2 * (d - 1) / dtld;

$PrePrint = ScreenDollarIndices;
(* d-dimensional Newton's constant *) 
DefConstantSymbol[G];
(* only one metric per one manifold defined *)
(* there's an issue here with delta *)
DefMetric[+1, \[Delta][-i, -j], CD, {",", "\[PartialD]"}, FlatMetric->True];
(* time as worldline parameter *)
DefParameter[t];
(* metric as tensors on flat manifold *)
DefTensor[gtt[], {Mflat, t}];
DefTensor[guptt[], {Mflat, t}];
DefTensor[gt[i], {Mflat, t}];
DefTensor[gupt[i], {Mflat, t}];
DefTensor[g[-i, -j], {Mflat, t}, Symmetric[{-i, -j}]];
DefTensor[gup[i, j], {Mflat, t}, Symmetric[{i, j}]];
(* tetrads defined as mixed tensors *)
DefTensor[enn[], {Mflat, t}];
DefTensor[ein[i], {Mflat, t}];
DefTensor[eni[i], {Mflat, t}];
DefTensor[eij[i, j], {Mflat, t}];
(* Kaluza-Klein fields *)
DefTensor[\[Phi][], {Mflat, t}];
DefTensor[A[-i], {Mflat, t}];
DefTensor[\[Sigma][-i, -j], {Mflat, t}, Symmetric[{-i, -j}]];
DefTensor[\[Sigma]up[i, j], {Mflat, t}, Symmetric[{i, j}]];
DefTensor[det\[Gamma][], {Mflat, t}];
(* worldline tensors *)
DefConstantSymbol[m];
$Assumptions = {m > 0};
DefTensor[v[i], {Mflat, t}];
DefTensor[S[i, j], {Mflat, t}, Antisymmetric[{i, j}]];
DefTensor[St[i],{Mflat, t}];
DefTensor[a1[i],{Mflat, t}];
(* PN order parameter *)
DefConstantSymbol[
    cInv, PrintAs -> "(\!\(\*SuperscriptBox[\(c\), \(-1\)]\))"
];
(* field counter parameter *)
DefConstantSymbol[Nf, PrintAs -> "(Nf)"];


(* ::Section::Closed:: *)
(*d + 1 independent of xTensor*)


(* Module with its local symbols used for dummy indices *)
Sumd1[a_][e_] := Module[{i}, ((e/.a -> i) + (e/.a -> n))];
(* recursive definition for more than 1 index to sum *)
Sumd1[a_, b__][e_] := Sumd1[b] [Sumd1[a][e]];


(* Christoffel symbol of 1st kind: all indices down *)
Chr1[a_, b_, c_] := 1/2 * (
    Der[b] @ gd1[c, a] + Der[c] @ gd1[a, b] - Der[a] @ gd1[b, c]
);
(* Christoffel symbol of 2nd kind: 1st index up *)
Chr2[a_, b_, c_] := (
    Module[{b1}, gd1[a, b1] * Chr1[-b1, b, c]//Sumd1[b1]]
);
Riem[c_, -a_, -c1_, -b_] := (
    Der[-c1] @ Chr2[c, -a, -b] - Der[-b] @ Chr2[c, -a, -c1]
    + Module[{b1}, Sumd1[b1][(
        Chr2[c, -b1, -c1] * Chr2[b1, -a, -b] 
        - Chr2[c, -b1, -b] * Chr2[b1, -a, -c1]
        )]
    ]
);


(* ::Section::Closed:: *)
(*Split to d and 1 into xTensor*)


TodPlus1[e_] := e/.{
    gd1[-n, -n] :> gtt[],
    gd1[n, -n] :> 1, 
    gd1[n, n] :> guptt[],
    gd1[-i_, -n] :> gt[-i], 
    gd1[-n, -j_] :> gt[-j], 
    gd1[i_, n] :> gupt[i], 
    gd1[n, j_] :> gupt[j], 
    gd1[-i_, n] :> 0,
    gd1[n, -j_] :> 0, 
    gd1[i_, -n] :> 0,
    gd1[-n, j_] :> 0,
    gd1[-i_, -j_] :> g[-i, -j], 
    gd1[-i_, j_] :> -\[Delta][-i, j], 
    gd1[i_, -j_] :> -\[Delta][i, -j], 
    gd1[i_, j_] :> gup[i, j]
}/.{ 
    ud1[n] :> 1, 
    ud1[i_] :> v[i], 
    ud1[-i_] :>v[-i], 
    Sd1[-n, -n] :> 0,
    Sd1[-n, -i_] :> -St[-i], 
    Sd1[-i_, -n] :> St[-i] , 
    Sd1[-i_, -j_] :> S[-i, -j]
}/.{
    ed1[n, -n] :> enn[], 
    ed1[n, -i_] :> eni[-i], 
    ed1[i_, -n] :> ein[i], 
    ed1[i_, -j_] :> eij[i, -j]
}/.{
    Der[-n] :> ParamD[t], 
    Der[n] :> ParamD[t], 
    Der[i_] :> CD[i]
};


(* ::Section::Closed:: *)
(*To KK*)


ToKK[e_] := e/.{
    gtt[] :> Exp[2\[Phi][]],
    gt[i_] :> -Exp[2\[Phi][]] * A[i],
    g[i_, j_] :> (
        -Exp[-2\[Phi][] / dtld] * (\[Delta][i, j] 
        + \[Sigma][i, j]) + Exp[2\[Phi][]] * A[i] * A[j]
    ),
    guptt[] :> ( 
        Exp[-2\[Phi][]] - Exp[2\[Phi][] / dtld] * Scalar[(\[Delta][i, j] 
        + \[Sigma]up[i, j]) * A[-i] * A[-j]]
    ),
    gupt[i_] :> (
        -Exp[2\[Phi][] / dtld] * Module[{j}, (\[Delta][i, j] 
        + \[Sigma]up[i, j]) * A[-j]]
    ),
    gup[i_, j_] :> -Exp[2\[Phi][] / dtld] * (\[Delta][i, j] + \[Sigma]up[i, j])
}/.{
    \[Sigma]up[i_, j_] :> Module[{l}, -\[Sigma][i, j] + \[Sigma][i, l] * \[Sigma][-l, j]],
    det\[Gamma][] :> (
        1 + Scalar[\[Sigma][i, -i]] + 1/2 * Scalar[\[Sigma][i, -i]]^2 
        - 1/2 * Scalar[\[Sigma][-i, -j] * \[Sigma][i, j]]
    )
}/.{
    enn[] :> Exp[\[Phi][]], 
    ein[i_] :> 0,
    eni[i_] :> -Exp[\[Phi][]] * A[i], 
    eij[i_, j_] :> Exp[-\[Phi][] / dtld] * (
        Module[
            {l}, \[Delta][i, j] + 1/2 * \[Sigma][i, j] - 1/8 * \[Sigma][i, l] * \[Sigma][-l, j]
        ]
    )
};


(* ::Text:: *)
(*(* the inverse of \[Sigma]ij and det\[Gamma] are expanded to the specific desired order, *)
(*   and in the spatial tetrad eij the symmetric root of \[Gamma]=\[Delta]+\[Sigma] is expanded *)
(*   to the specific desired order, may be upgraded to exact definition *)*)


(* ::Section::Closed:: *)
(*To PN*)


ToPN[e_] := e/.{ 
    \[Phi][] :> cInv^2 * \[Phi][],
    A[i_] :> cInv^3 * A[i],
    \[Sigma][i_, j_] :> cInv^4 * \[Sigma][i, j]
}/.{
    v[i_] :> cInv * v[i],
    S[i__] :> cInv * S[i], 
    St[i_] :> cInv^2 * St[i],
    a1[i_] :> cInv^2 * a1[i]
}/.{
    ParamD[p:t..][ex_] :> cInv^Length[{p}] * ParamD[p][ex]
};


PN[ord_][e_] := Series[e, {cInv, 0, ord}]//Normal;


CommuteParamD[e_] := e//.{
    ParamD[t]@CD[i_] @ ex_ :> CD[i] @ ParamD[t] @ ex
};


SimpFast[e_] := e//CommuteParamD//ToCanonical;
Simp[e_] := Collect[e//SimpFast, {cInv, \[Phi][], \[Phi][]^_, Scalar[_]}, Simplify]; 


Contract[e_] := e//NoScalar//ContractMetric//PutScalar;
SetOptions[ContractMetric, {AllowUpperDerivatives -> True}];


(* ::Section::Closed:: *)
(*Field*)


NfCount[e_] := e/.{ 
    \[Phi][] :> Nf * \[Phi][],
    A[i_] :> Nf * A[i],
    \[Sigma][i_, j_] :> Nf * \[Sigma][i, j]
};
NfSeries[ord_][e_] := Series[e//NfCount, {Nf, 0, ord}]//Normal;
NfInt[ord_][e_] := NfSeries[ord][e] - NfSeries[2][e]/.Nf -> 1;
FlipDer[e_] := e/.{
    ParamD[t, t] @ (ex1_) * ex2_ :> -ParamD[t] @ ex1 * ParamD[t] @ ex2,
    CD[i_] @ ParamD[t] @ (ex1_) * ex2_ :> -CD[i] @ ex2 * ParamD[t] @ ex1,
    CD[i_] @ CD[j_] @ (ex1_) * ex2_ :> -CD[i] @ ex2 * CD[j] @ ex1
};


Sfieldint = (
    -cInv^-4 / (16\[Pi] G) * Sqrt[Exp[-2(d / dtld - 1) * \[Phi][]] * det\[Gamma][]] * (
        (gd1[a, c] * Riem[b, -a, -b, -c]//Sumd1[c, a, b])
        - 1/2 * (
            gd1[a, b1] * Chr1[-a, -b, -c] * gd1[b, c] * (
                Chr1[-b1, -c1, -b2] * gd1[c1, b2]
            )//Sumd1[a, b, c, b1, b2, c1]
        )
    )
    //TodPlus1//SimpFast//ToKK//NoScalar//ToPN//PN[6]//Simp//NfInt[4]
    //Expand//FlipDer//ContractMetric//PutScalar//Simp
);


(* total time derivatives can be added to simplify or modify form of 
   field part *)
TD = (
    Module[{i, j}, cInv^6 / (16\[Pi] G) * ParamD[t][
        -1/2 * A[i] * A[-i] * CD[-j][A[j]] 
        - 2 / (2 - d) * CD[-i][\[Phi][]] * A[-j] * \[Sigma][i, j] 
        + 1 / (2 - d) * CD[-i][\[Phi][]] * A[i] * Scalar[\[Sigma][j, -j]]
        ]
    ]//SimpFast//FlipDer//Simp
);
SfieldintTD = ( 
    (Sfieldint + TD)//SimpFast//NoScalar//Simp//Expand//ContractMetric
    //PutScalar//Simp
);


(* ::Text:: *)
(*(* Pinv[i_, j_, k_, i1_] := 1/2( *)
(*    delta[i, k] * delta[j, i1] + delta[i, i1] * delta[j, k] *)
(*    - delta[i, j] * delta[k, i1]*)
(*    ) *)
(*   quadratic operator of the tensor field in action-does not depend on *)
(*   the dimension d *) *)
(*(* P[i_, j_, k_, i1_] := 1/2( *)
(*    delta[i, k] * delta[j, i1] + delta[i, i1] * delta[j, k] *)
(*    + (2 - cd) * delta[i, j] * delta[k, i1]*)
(*   )*)
(*   projector-the inverse, giving the index structure of the propagtor of *)
(*   the tensor field *) *)


(* ::Section::Closed:: *)
(*Mass*)


Swlmass = (
    -m * cInv^-2 * Sqrt[gd1[-a, -b] * ud1[a] * ud1[b]//Sumd1[a, b]]
    //TodPlus1//ToKK//ToPN//SimpFast//PN[6]//Contract//Simp
);


(* ::Section::Closed:: *)
(*Spin*)


SetOptions[MakeRule, MetricOn -> All];
(* why constant? only up to finite size effects *)
DefConstantSymbol[u]; 
Insertu[e_] := e/.u -> Swlmass / (-m * cInv^-2);


(* IndexSolve that follows, does not work on tensor with 
   contracted indices, so indices should be contracted first *)
CnnSSC = (
    \[Delta][i, j] * (
        Sumd1[a, b][Sd1[-j, -a] * ed1[a, -b] * ud1[b]] 
        + u * Sd1[-j, -n]//TodPlus1//ToKK//ToPN
    )//ContractMetric//Simp
);
(* insertu is not essential here *)
CnnRule = IndexSolve[CnnSSC == 0, St[i]]//Insertu;
InsertCnnSSC[e_] := e/.CnnRule;


(* Insertu is for the 2nd term here *)
spinv = ( 
    cInv^-1 * (
        (
            -1/2 * Sd1[-a, -b] * ed1[b, -c] * gd1[c, b1] * (
                Der[-c1] @ ed1[a,-b1] 
                - Sumd1[b2][Chr2[b2, -c1, -b1] * ed1[a, -b2]]
            )* ud1[c1]//Sumd1[a, b, c, b1, c1]
         )-(
             Sd1[-a, -b] * ed1[b, -c] * ud1[c] * ed1[a, -b1] * ( 
                 Chr2[b1, -b2, -c1] * ud1[b2] * ud1[c1] / u^2
             )//Sumd1[a, b, c, b1, b2, c1]
         ) 
     )//TodPlus1//SimpFast//ToKK//ToPN//InsertCnnSSC//Insertu//PN[7]
     //Contract//Simp
);


Swlspin1 = (
    spinv - (
        cInv^-1 * a1[i] * ed1[a, -i] * Sd1[-a, -b] * ed1[b, -c] * (
            ud1[c] / u^2
        )//Sumd1[a, b, c]//TodPlus1//SimpFast//ToKK//ToPN//InsertCnnSSC
        //Insertu//PN[7]
    )//Contract//Simp
);


(* ::Section::Closed:: *)
(*Spin-Squared*)


SortCovDsStart[CD];
DefConstantSymbol[CES2];


DefTensor[s[i], {Mflat, t}];
ToSVec[e_] := e/.S[i_, j_] :> Module[{l}, epsilon\[Delta][i, j, l] * s[-l]];


(* ::Text:: *)
(*(* on this section the spin is not the local hatted one as assumed for *)
(*   the linear in spin section, but to begin with, it is the general *)
(*   covariant one *) *)


(* transforming to the local hatted spin *)
ToSHat[e_] := e/.Sd1[-a_, -b_] :> (
    Sd1[-a, -b] - 1 / u^2 * Module[{c, c1}, (
        Sd1[-a, -c] * ud1[c] * ud1[c1] * gd1[-c1, -b]
        - Sd1[-b, -c] * ud1[c] * ud1[c1] * gd1[-c1, -a]
    )//Sumd1[c, c1]]
);
ToSHLoc[e_] := e/.Sd1[-a_, -b_] :> Module[
    {c, c1}, Sd1[-c, -c1] * ed1[c, -a] * ed1[c1, -b]//Sumd1[c,c1]
];


(* TermByTerm[transfo_][e_Plus] := Module[
       {terms,result},terms=Expand[e];result=transfo/@terms], may speed it *)
Swlspin2 = (
    1 / (2m) * Riem[c, -a, -b1, -b] * ud1[a] * ud1[b] / u * (
        Sd1[-c, -b2] * gd1[b2, b3] * Sd1[-b3, -b4] * gd1[b4, b1]
    )//Sumd1[a, b, c, b1, b2, b3, b4]//ToSHat//ToSHLoc//TodPlus1//ToKK
    //ToPN//Insertu//InsertCnnSSC//PN[8]//Contract//Simp
);


Swlspin2vec = Swlspin2//ToSVec//Contract//Simp;
Swlspin2vec/.d -> 3;


(* ::Section:: *)
(*Cubic Spin*)


(* ::Section:: *)
(*Quartic Spin*)


(* ::Section::Closed:: *)
(*Export *)


SetDirectory[NotebookDirectory[]];


SfieldintTD >> "frules_field.dat.m";
Swlmass + Swlspin1 + CES2 * Swlspin2 >> "frules_wl.dat.m";
