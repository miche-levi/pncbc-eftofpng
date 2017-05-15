(* ::Package:: *)

(* ::Title:: *)
(*Coding Style*)


(* ::Text:: *)
(*The coding style should not play an exaggerated role for a code. However, a uniform style greatly improves the readability of a code, just like a uniform spelling of words improves the readability of a text. The purpose of this document is to fix a few simple style rules that should be easy to follow, so that one can focus on the actual work. Another goal is to remove uminportant noise from git commits. The coding style should in general be followed for contributions to EFTtoPNG.*)


(* ::Text:: *)
(*git pre-commit hooks can and should be used to check and apply some of the conventions automatically before each commit.*)


(* ::Subsection:: *)
(*File types and names*)


(* ::Text:: *)
(*Code must be saved as "Wolfram Mathematica Package", that is, .m files. This enables a proper use of git. Code should be in code cells (white background), as opposed to input cells (gray background). Input cells can be used for examples, documentation etc. Long comments go into text cells.*)


(* ::Text:: *)
(*Mathematica expressions that are generated/exported by some code (like final results) should have an extension .dat.m in order to distinguish them from the code.*)


(* ::Subsection:: *)
(*Indentation and spaces*)


(* ::Text:: *)
(*Since code is saved in the .m instead of the .nb format, indentation can and has to be done manually. This is the most important part of styling the code. The purpose is to make blocks of code that belong together clearly visible. For instance, when having different levels of braces, a good formatting is something like this:*)


L = (
	G / r (m1 + m2)
	+ G^2 / r^2 (
		2 / c^2 (m1 / m2 - v^2)
		+ 7 / c^4 (v^2 - 3 v^4)
	)
);


(* ::Text:: *)
(*Of course, everything can be cramped into a single line here, but consider that code rarely gets less readable by splitting over several lines together with a clear indentation. There are no strict rules for how to indent, but use some common sense, keep it simple, and immitate the way the existing code is indented.*)


(* ::Text:: *)
(*Code cells and functions/expressions should in general not span more than ca 50 lines. Functions which perform a complicated task should in fact at most be a few lines long. Each code cell may collect a few functions that logically belong together.*)


(* ::Text:: *)
(*There are a few rules which should in general be followed:*)


(* ::Item:: *)
(*Indentation should be done using tabs (which corespond to 4 spaces in the Mathematica frontend).*)


(* ::Item:: *)
(*All binary operators like = + @ should be preceded and followed by a space, except for powers, e.g., x^2.*)


(* ::Item:: *)
(*Postfix operators should not be preceded by a space, e.g., the factorial. Conversely, prefix operators should not be followed by a space. The latter is not strict for the minus, since it can also play the role of a binary operator.*)


(* ::Item:: *)
(*Commas should be followed by a space.*)


(* ::Item:: *)
(*Comments in the code should be surrounded by spaces: (* this is a short comment *)*)


(* ::Item:: *)
(*Unnecessary spaces at the end of lines should be removed.*)


(* ::Subsection:: *)
(*Miscellanea*)


(* ::Item:: *)
(*Following standard Mathematica practice, functions are named in CamelCase (a concatenation of individual words beginning with a capital letter). Global variables are additionally preceded by a dollar. Names should be as concise as possible without becoming cryptic.*)


(* ::Item:: *)
(*Lines should be at most 80 characters long (tabs counting as 4 characters).*)


(* ::Item:: *)
(*Before committing a package file to git, close all subsection, subsubsections etc so that only a "table of contents" showing the main sections is shown. These main sections should be of type Section or Subchapter.*)


(* ::Item:: *)
(*Commands should always be ended by a semicolon. (Except in example computations where the output is of interest.)*)


(* ::Item:: *)
(*Do not put several commands (separated by a semicolon) into a single line.*)


(* ::Subsection:: *)
(*Further reading*)


(* ::Text:: *)
(*The coding style of the linux kernel (https://github.com/torvalds/linux/blob/master/Documentation/process/coding-style.rst) is a good resource for general advice on how to write readable code, in particular sections 1, 2, 6, and 8, which are less specific to C.*)
