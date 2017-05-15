(* ::Package:: *)

(* ::Title:: *)
(*Package EFTofPNG version 0.99*)


(* ::Chapter:: *)
(*EFTofPNG: FeynGen*)


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


(* ::Section::Closed:: *)
(*define vertices manifold and metric*)


(* load xTensor package *)
Needs["xAct`xTensor`"];
$DefInfoQ = False;
$UndefInfoQ = False;


(* define manifold of vertices with 2-point function as metric *)
DefConstantSymbol[dV];
DefManifold[Vertices, dV, {A1, A2, A3, A4, A5, A6, A7, A8, A9, A10}];
DefMetric[1, gV[-A1, -A2], DV, {",", "\[PartialD]"}, FlatMetric -> True];


(* ::Section::Closed:: *)
(*define generic vertices*)


(* symmetry of vertex with different fields *)
FVertexSymmetry[
    {}, start_Integer:2, sym_StrongGenSet:Symmetric[{}, Cycles]
] := sym;
FVertexSymmetry[
    {num_Integer, next___}, start_Integer:2, 
    sym_StrongGenSet:Symmetric[{}, Cycles]
]:= FVertexSymmetry[
	{next}, start+num,
	JoinSGS[sym, Symmetric[Range[start, start + num - 1], Cycles]]
];


(* define vertices. T: for topologies, F: with fields inserted *)
(* bulk field vertices *)
DefTensor[VertexT[AnyIndices @ TangentVertices], Vertices];
SymmetryGroupOfTensor[VertexT[indices___]] ^:= Symmetric[
    Range @ Length @ {indices}, Cycles
];
DefTensor[VertexF[LI[], AnyIndices @ TangentVertices], Vertices];
SymmetryGroupOfTensor[VertexF[LI[nums___], ___]] ^:= FVertexSymmetry[
    {nums}
];


(* worldline 1 vertices *)
DefTensor[Wl1T[AnyIndices @ TangentVertices], Vertices];
SymmetryGroupOfTensor[Wl1T[indices___]] ^:= Symmetric[
    Range @ Length @ {indices}, Cycles
];
DefTensor[Wl1F[LI[], AnyIndices @ TangentVertices], Vertices];
SymmetryGroupOfTensor[Wl1F[LI[nums___], ___]] ^:= FVertexSymmetry[
    {nums}
];


(* worldline 2 vertices *)
DefTensor[Wl2T[AnyIndices @ TangentVertices], Vertices];
SymmetryGroupOfTensor[Wl2T[indices___]] ^:= Symmetric[
    Range @ Length @ {indices}, Cycles
];
DefTensor[Wl2F[LI[], AnyIndices @ TangentVertices], Vertices];
SymmetryGroupOfTensor[Wl2F[LI[nums___], ___]] ^:= FVertexSymmetry[
    {nums}
];


(* ::Section::Closed:: *)
(*generic tools*)


(* convert sum of terms to list and vice versa *)
PlusToList[e_Plus] := List @@ e;
PlusToList[e_] := {e};
ListToPlus[l_List] := Plus @@ l;


(* apply transformation term by term, with optional status bar *)
TermByTerm[transfo_, bar_: True][terms_List] := Module[
	{
		numterms, count = 0, result, time
	},
    numterms = Length[terms];
    If[bar,
		Print["Number of terms: ", numterms];
		Print[ProgressIndicator[Dynamic[count], {0, numterms}]];
	];
	time = Timing[result = (count++; transfo[#]) & /@ terms;]//First;
	If[bar, Print["Time: ", time, " s"];];
	result
];
TermByTerm[transfo_, bar_: False][e_] := (
    e//PlusToList//TermByTerm[transfo, bar]//ListToPlus
);


(* timing function *)
Needs["Units`"];
TimeIt[ex_] := Module[
	{
		time
	},
	time = First @ Timing[ex];
	timing == If[time < 60.0,
		Round[time, 0.1] Second,
		If[time < 60.0 60.0,
			Round[time / 60, 0.1] Minute,
			Round[time / 60 / 60, 0.1] Hour
		]
	]
];
SetAttributes[TimeIt, HoldFirst];


(* ::Subchapter::Closed:: *)
(*Generate Graph Topologies*)


(* ::Section::Closed:: *)
(*generate vertex combinations*)


(* Q-functions for vertex types *)
FeynVertexQ[v_] := MemberQ[
    {VertexT, VertexF, Wl1T, Wl1F, Wl2T, Wl2F}, v
];
WlVertexQ[v_] := MemberQ[{Wl1T, Wl1F, Wl2T, Wl2F}, v];


(* generate unique indices for each of the vertices *)
InsertVertexIndex[expr_] := expr/.{ v_?FeynVertexQ[inds___] :> (
    Unique /@ v[inds]
)};
(* 1/n! factor from Exp in path integral *)
PermuteVertexFactor[expr_List] := MapIndexed[
    #1 / (#2[[1]] - 1)! &, expr
];
(* add vertices up to a certain power *)
AddVertices[vertex_, Vlist_List, relevantQ_] := If[
    relevantQ[vertex], 
    FixedPointList[
        Select[# * InsertVertexIndex[vertex], relevantQ] &, Vlist
    ],
    {Vlist}
] // PermuteVertexFactor // Flatten;
(* generate product of vertices up to a certain power *)
GenerateVertices[VlistInput_List, relevantQ_] := Drop[
    Fold[AddVertices[#2, #1, relevantQ]&, {1}, VlistInput], 1
];


(* ::Section::Closed:: *)
(*generate contractions of vertices*)


(* build combinations of gV for all contractions of inds *)
ContractAll[{A1_, A2_}] := gV[A1, A2];
ContractAll[inds_] := Module[
	{
		lastinds = Drop[inds, 1]
	},
    If[OddQ[Length[inds]],
	   0,
	   Expand[ Plus @@ Flatten @ Table[
           gV[inds[[1]], lastinds[[j]]] * (
               ContractAll[Drop[lastinds, {j}]]
           ), 
	       {j, Length[lastinds]}
       ]]
   ]
];


(* build all contractions of indices for given expr *)
Contractor[expr_] := (
    -FindFreeIndices[expr]/.{IndexList -> List}//ContractAll
);
ContractVertices[expr_] := (
    expr * Contractor[expr]//ContractMetric//ToCanonical
);


(* ::Section::Closed:: *)
(*filter relevant topologies*)


(* introduce order parameters to classify topologies:
   number of propagators, vertices, worldlines *)
DefConstantSymbol /@ {propa, vertex, wl1, wl2};
UncountTopology[expr_] := expr/.{
    propa -> 1, vertex -> 1, wl1 -> 1, wl2 -> 1
};
CountTopology[expr_] := UncountTopology[expr]/.{
	v_?FeynVertexQ[i___] :> propa^Length[{i}] * vertex * v[i]
} /. {
	Wl1T[i___] :> wl1 * Wl1T[i], Wl2T[i___] :> wl2 * Wl2T[i]
};


(* get topologies which are tree level and with 2 worldlines. 
   call before contractions *)
FilterClassicalTopology[expr_] := Select[
    expr//CountTopology, (
        EvenQ[Exponent[#, propa]] && 
        Exponent[#, propa] / 2 - Exponent[#, vertex] <= -1 &&
	    Exponent[#, wl1] >= 1 && Exponent[#, wl2] >= 1 
    )&
]//UncountTopology;


(* drop UV renormalization topologies *)
SplitWlVertex[expr_] := expr /. {
	v_?WlVertexQ[inds___] :> Times @@ (v /@ {inds}) 
}//BreakScalars//PutScalar;
TestRenormalization[expr_] := SplitWlVertex[expr] /. {
	Scalar[x_] :> If[
        FilterClassicalTopology[{x}] === {}, 0, Scalar[x]
    ]
};
DropRenormalization[expr_] := TermByTerm[
    If[TestRenormalization[#]===0, 0, #]&
][expr//Expand];


(* drop unconnected topologies *)
DropUnconnected[expr_] := PutScalar[expr]/.{
    Scalar[x_] * Scalar[y_] -> 0, Scalar[_]^_ -> 0
};


(* ::Section::Closed:: *)
(*generate topology graphs*)


(* generate graph corresponding to contraction *)
MakeGraphTerm[expr_] := Module[
	{ex, wl1, wl2, v},
    (* adding ``past'' tip points to the worldlines *)
	ex = expr * wl1[Unique[]] * wl2[Unique[]] /. {
		Wl1T[inds___] :> v[Unique[], wl1][inds],
		Wl2T[inds___] :> v[Unique[], wl2][inds],
        VertexT[inds___] :> v[Unique[]][inds]
	} //. {
		wl1[i___] * v[tg_, wl1][j___] :> wl1[i, tg] * v[tg][j],
		wl2[i___] * v[tg_, wl2][j___] :> wl2[i, tg] * v[tg][j]
	} /.{(* adding ``future'' tip points to the worldlines *)
        wl1[i__] :> wl1[{i, Unique[]}], wl2[i__] :> wl2[{i, Unique[]}]
    };
	ex = Reap[ex //. {
		wl1[l_List] :> Times @@ (Sow /@ Table[
            Style[UndirectedEdge[l[[i]], l[[i + 1]]], 
                {Thickness[.015], Black}
            ],
            {i, 1, Length[l] - 1}
        ]),
		wl2[l_List] :> Times @@ (Sow /@ Table[
            Style[UndirectedEdge[l[[i]], l[[i + 1]]], {Thick, Black}],
            {i, 1, Length[l] - 1}
        ]),
        v[tg1___][i1___, A_, i2___] * v[tg2___][i3___, -A_, i4___] :> 
            (Sow[UndirectedEdge[tg1, tg2]] * v[tg1][i1, i2] 
            * v[tg2][i3, i4]
        )
	}];
	{ex[[1]] /. {
        v[___][] -> 1, UndirectedEdge[___] -> 1, Style[___] -> 1
     },
	 Graph[ex[[2, 1]]]}
];


(* generate graphs corresponding to sum of contractions *)
MakeGraphs[expr_] := MakeGraphTerm /@ PlusToList[
    expr//Expand//NoScalar
];


(* ::Section::Closed:: *)
(*Example: Topologies to G^3*)


DefConstantSymbol[G];


(* vertices with powers in G and usual combinatoric factors *)
VerticesG = Block[{rG = Sqrt[G], n = 3}, {
    (rG^# / #! * Wl1T @@ (
        Symbol @ StringJoin["A", ToString[#]]& /@ Range[#]
    ))& /@ Range[n],
	(rG^# / #! * Wl2T @@ (
        Symbol @ StringJoin["A", ToString[#]]& /@ Range[#]
    ))& /@ Range[n],
	(rG^(#) / (# + 2)! * VertexT @@ (
        Symbol @ StringJoin["A", ToString[#]]& /@ Range[# + 2]
    ))& /@ Range[n - 1]
}//Flatten];


(* generate combinations of vertices to G^3 *)
vert = GenerateVertices[VerticesG, Exponent[#, G] <= 3&];
(* filter combinations with 2 worldlines and even props before 
   contraction *) 
vertf = FilterClassicalTopology[vert];
(* generate contractions *)
contract = vertf//TermByTerm[ContractVertices, True]//ListToPlus;
(* further filter contractions *)
contractf = Collect[contract//DropRenormalization//DropUnconnected, G];
(* generate topology graphs up tp G^3 *)
MakeGraphs[G^# * Coefficient[contractf, G, #]]& /@ Range[3]


(* ::Subchapter::Closed:: *)
(*Generate PN Diagrams*)


(* ::Section::Closed:: *)
(*insert propagators and fields *)


(* define NRG field propagators *)
DefTensor[Prop\[Phi][-A1, -A2], Vertices, Symmetric[{-A1, -A2}]];
DefTensor[PropA[-A1, -A2], Vertices, Symmetric[{-A1, -A2}]];
DefTensor[Prop\[Sigma][-A1, -A2], Vertices, Symmetric[{-A1, -A2}]];


PropList = {Prop\[Phi], PropA, Prop\[Sigma]};
PropagatorQ[s_] := MemberQ[PropList, s];


(* label vertices with fields *)
ConvertVertices[expr_] := Module[{sow},
	expr /. {
		Wl1T[i___] :> Wl1F[LI[], i],
		Wl2T[i___] :> Wl2F[LI[], i],
        VertexT[i___] :> VertexF[LI[], i]
	} //. {
		prop_?PropagatorQ[i1___, -A1_, i2___] * (
            vF_[LI[x___], A1_, i3___]
        ) :>
        prop[i1, -A1, i2] * vF[LI[x, sow[A1, prop]], i3]		
	} /. {
		vF_?FeynVertexQ[LI[x___]] :> Module[
			{ilist = Flatten /@ Last @ Reap[
                {x} /. sow -> Sow, PropList
            ]},
			vF[LI @@ Length /@ ilist, Sequence @@ Join @@ ilist]
		]
	}
];


(* reinstate 2-point function to contracted vertices *)
ShowPropagators[expr_] := expr //. {
	v_?FeynVertexQ[i1___, -i_, i2___] :> Module[
        {A1}, gV[-i, -A1] * v[i1, A1, i2]
    ]
};


ToCanonicalDiagrams[expr_] := ToCanonical[
    expr, UseMetricOnVBundle -> None
];


(* insert propagators and fields *)
InsertFields[expr_] := NoScalar[expr // ShowPropagators] /. {
	gV[A1_, A2_] :> Prop\[Phi][A1, A2] + PropA[A1, A2] + Prop\[Sigma][A1, A2]
} // ToCanonicalDiagrams // ConvertVertices;


(* ::Section::Closed:: *)
(*project to spin orders*)


(* order parameter for mass and spin sectors *)
DefConstantSymbol[SO];


(* cut worldline vertex according to spin order *)
SpinProjectorList = {mPart, SPart, SSPart};
DefInertHead /@ SpinProjectorList;
partRules = {
	mPart[ex_] :> (ex /. SO -> 0),
	SPart[ex_] :> Coefficient[ex, SO, 1],
	SSPart[ex_] :> Coefficient[ex, SO, 2]
};
SpinProjectorQ[sym_] := MemberQ[SpinProjectorList, sym];


(* projecting generated diagrams to spin sectors *)
ProjectSpin[expr_] := expr /. {
	wl_?WlVertexQ[x___] :> (
        mPart @ wl[x] + SO * SPart @ wl[x] 
        + SO^2 * SSPart @ wl[x]
    )
};


(* ::Section::Closed:: *)
(*import Feynman rules and PN count*)


(* PN counting parameter *)
DefConstantSymbol[cInv, PrintAs -> "(\*SuperscriptBox[c, -1])"];
(* order parameters to count NRG fields *)
DefConstantSymbol[\[Phi]];
DefConstantSymbol[A];
DefConstantSymbol[\[Sigma]];


(* import Feynman rules while adjusting counting of spin and fields *)
CountingFreeQ[expr_] := And @@ (
    FreeQ[expr, #]& /@ {G, SO, cInv, \[Phi], A, \[Sigma]}
);
ImportRulesFD[file_] := Collect[Module[{pd, \[Phi]f, Af, \[Sigma]f},
	Get[file] //. {
        ParamD[___] :> pd, S[__] -> SO, \[Phi][i___] :> \[Phi] * \[Phi]f[i], 
        A[i___] :> A * Af[i], \[Sigma][i___] :> \[Sigma] * \[Sigma]f[i]
    } //. {
		Scalar[c_ X_] /; MemberQ[{SO, \[Phi], A, \[Sigma]}, c] :> c * Scalar[X],
		CD[i_][c_ X_] /; MemberQ[{SO, \[Phi], A, \[Sigma]}, c] :> c * CD[i][X],
		pd[c_ X_] /; MemberQ[{SO, \[Phi], A, \[Sigma]}, c] :> c * pd[X]
		} /. { A -> A / cInv, \[Sigma] -> \[Sigma] / cInv^2 }],
	{G, SO, cInv, \[Phi], A, \[Sigma] },
	(If[Not @ CountingFreeQ[#], Throw[#]]; 1)&
];
frulesFD = ImportRulesFD["frules_field.dat.m"];
wlrulesFD = ImportRulesFD["frules_wl.dat.m"];


(* count PN order of vertex while sorting to spin secors *)
VertexCountPN[rules_, head_, nums___] := head[Fold[
	Coefficient[#1, Sequence @@ #2]&,
	rules,
	Thread[{ {\[Phi], A, \[Sigma]}, {nums} }]
]] /. partRules // (Exponent[#, cInv, Min]&) // (
    If[# === \[Infinity], 0, cInv^#]&
);


(* count PN orders of all vertices *)
HidePNOrder[expr_] := expr /. { cInv -> 1 };
ShowPNOrder[expr_] := HidePNOrder[expr] /. {
	proj_?SpinProjectorQ @ Wl1F[LI[nums___], i___] :> ( 
        VertexCountPN[wlrulesFD, proj, nums] * (
            proj @ Wl1F[LI[nums], i]
        )
    ),
	proj_?SpinProjectorQ @ Wl2F[LI[nums___], i___] :> (
        VertexCountPN[wlrulesFD, proj, nums] * (
            proj @ Wl2F[LI[nums], i]
        )
    ),
	Wl1F[LI[nums___], i___] :> VertexCountPN[
        wlrulesFD, Identity, nums
    ] * Wl1F[LI[nums], i],
	Wl2F[LI[nums___], i___] :> VertexCountPN[
        wlrulesFD, Identity, nums
    ] * Wl2F[LI[nums], i],
    (* propagator time insertions not included in Feynamn rules files,
       should come before generic vertex from file to be accounted for *)
	VertexF[LI[nums___], i1_, i2_] :> cInv^2 * (
        VertexF[LI[nums], i1, i2]
    ),
	VertexF[LI[nums___], i___] :> VertexCountPN[
        frulesFD, Identity, nums
    ] * VertexF[LI[nums], i]
};


(* ::Section::Closed:: *)
(*add propagator insertions*)


(* add propagator time insertions, 
   not included in the Feynamn rules file *)
PropagatorInsertions[0][expr_] := expr;
PropagatorInsertions[n_?Positive][expr_] := Module[
	{
		ilabel
	},
    ilabel[Prop\[Phi]] = LI[2, 0, 0];
	ilabel[PropA] = LI[0, 2, 0];
	ilabel[Prop\[Sigma]] = LI[0, 0, 2];
	expr /. {
		p_?PropagatorQ[A1_, A2_] :> Module[{A3, A4},
			p[A1, A2] + PropagatorInsertions[n - 1][p[A1, -A3]] * ( 
                cInv^2 * VertexF[ilabel[p], A3, A4] * p[-A4, A2]
            )
		]
	}
];


(* ::Section::Closed:: *)
(*generate PN graphs*)


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
    }] // Last // Flatten;
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
        v[tg1___][i1___, A1_, i2___] * p_?PropagatorQ[-A1_, -A2_] * (
            v[tg2___][i3___, A2_, i4___]
        ) 
        :> Sow[Style[UndirectedEdge[tg1, tg2], pstyle[p]]] * (
            v[tg1][i1, i2] * v[tg2][i3, i4]
        )
	}];
	{ex[[1]] /. { 
        v[___][___] -> 1, UndirectedEdge[___] -> 1, Style[___] -> 1 
    },
	Graph[properties, ex[[2, 1]]] 
    }
];


(* generate graphs corresponding to sum of PN contractions *)
MakePNGraphs[expr_] := MakePNGraphTerm /@ PlusToList[
    expr// Expand//NoScalar
];


(* ::Section::Closed:: *)
(*Example: PN diagrams to G^3 and 4PN*)


(* cut at certain PN and spin orders *)
Cut2PN[expr_] := Collect[
    Series[expr, {cInv, 0, 4}] // Normal, {SO, cInv, G}
];
Cut3PN[expr_] := Collect[
    Series[expr, {cInv, 0, 6}] // Normal, {SO, cInv, G}
];
Cut4PN[expr_] := Collect[
    Series[expr, {cInv, 0, 8}] // Normal, {SO, cInv, G}
];
CutSpin[expr_] := Collect[
    Series[expr, {SO, 0, 2}] // Normal, {SO, cInv, G}
];


(* generate topology contractions up tp G^3 and put in fields *)
diagrams = contractf // Expand // TermByTerm[InsertFields, True]; 
(* cut contractions at 4PN order *)
PNdiagrams = diagrams // ShowPNOrder // Cut4PN;
(* add in up to 3 propagator insertions.
   In general this should be n insertions at nPN *)
PNdiagramsX = PNdiagrams // Expand // TermByTerm[
    (#//PropagatorInsertions[3]//Cut4PN//ToCanonicalDiagrams//Cut4PN)&,
    True
];
(* project to spin sectors and cut at quadratic in spin and 4PN *)
PNdiagramsS = PNdiagramsX // Expand // TermByTerm[
    (#//ProjectSpin//CutSpin//ShowPNOrder//Cut4PN//ToCanonicalDiagrams)&,
    True
]//Cut4PN;


(* set directory for output of graphs *)
SetDirectory[NotebookDirectory[]];
Put[PNdiagramsS, "PNdiagrams.dat.m"];


(* ::Subsection::Closed:: *)
(*point-mass diagrams*)


(* generate point-mass graphs to 2PN *)
Coefficient[PNdiagramsS, SO, 0] // Cut2PN;
MakePNGraphs[G^# * Coefficient[%, G, #]]& /@ Range[3]


(* ::Subsection::Closed:: *)
(*spin-orbit diagrams*)


(* generate spin-orbit graphs to NNLO *)
Coefficient[PNdiagramsS, SO, 1];
MakePNGraphs[G^# * Coefficient[%, G, #]]& /@ Range[3]


(* ::Subsection::Closed:: *)
(*spin-squared diagrams*)


(* generate quadratic in spin graphs to NNLO *)
Coefficient[PNdiagramsS, SO, 2];
MakePNGraphs[G^# * Coefficient[%, G, #]]& /@ Range[3]
