# Well-Behaved (Co)algebraic Semantics of Regular Expressions in Dafny
> Regular expressions are commonly understood in terms of their denotational semantics, that is, through formal languages -- the regular languages. This view is inductive in nature: two primitives are equivalent if they are constructed in the same way. Alternatively, regular expressions can be understood in terms of their operational semantics, that is, through deterministic finite automata. This view is coinductive in nature: two primitives are equivalent if they are deconstructed in the same way. It is implied by Kleene's famous theorem that both views are equivalent: regular languages are precisely the formal languages accepted by deterministic finite automata. In this paper, we use Dafny, a verification-aware programming language, to formally verify, for the first time, what has been previously established only through proofs-by-hand: the two semantics of regular expressions are well-behaved, in the sense that they are in fact one and the same, up to pointwise bisimilarity. At each step of our formalisation, we propose an interpretation in the language of Coalgebra. We found that Dafny is particularly well suited for the task due to its inductive and coinductive features and hope our approach serves as a blueprint for future generalisations to other theories.

## About this repository

This repository contains the source code accompanying the paper [Well-Behaved (Co)algebraic Semantics of Regular Expressions in Dafny](https://link.springer.com/chapter/10.1007/978-3-031-77019-7_3) by [Stefan Zetzsche](https://zetzsche.st) and [Wojciech Różowski](https://github.com/wkrozowski). To cite this repository you can currently use the following reference:
```  
@software{Zetzsche_Dafny-VMC_a_Library_2024,
author = {Zetzsche, Stefan and Rozowski, Wojciech},
title = {{Well-Behaved (Co)algebraic Semantics of Regular Expressions in Dafny}},
url = {https://github.com/zetzschest/DafnyWellBehavedCoalgebraicSemantics},
year = {2024}
}
```