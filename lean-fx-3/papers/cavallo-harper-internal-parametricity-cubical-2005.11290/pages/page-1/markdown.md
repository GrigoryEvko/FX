Logical Methods in Computer Science
Volume 17, Issue 4, 2021, pp. 5:1–5:60
https://lmcs.episciences.org/

Submitted May 25, 2020
Published Nov. 03, 2021

# INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

EVAN CAVALLO AND ROBERT HARPER

Department of Computer Science, Carnegie Mellon University, Pittsburgh, Pennsylvania, USA
e-mail address: {ecavallo,rwh}@cs.cmu.edu

ABSTRACT. We define a computational type theory combining the contentful equality structure of cartesian cubical type theory with internal parametricity primitives. The combined theory supports both univalence and its relational equivalent, which we call relativity. We demonstrate the use of the theory by analyzing polymorphic functions between higher inductive types, observe how cubical equality regularizes parametric type theory, and examine the similarities and discrepancies between cubical and parametric type theory, which are closely related. We also abstract a formal interface to the computational interpretation and show that this also has a presheaf model.

# INTRODUCTION

In the past decade or so, the study of dependent type theory has been transformed by a growing recognition of the importance of contentful (or proof-relevant) equality. At its root, the idea is simple: a proof of an equality is a piece of data. To go a bit a farther, a proof of equality may play a non-trivial role in computation. From the type-theoretic perspective, where the computational content of proofs has always been emphasized (“proofs as programs”), it is completely natural to think of equality this way. Nevertheless, it has been common to treat proofs of equality as irrelevant: we prove equalities to check code correctness or to prove a theorem, but we do not expect those proofs to influence how our code runs.

That expectation was shaken by Hofmann and Streicher’s groupoid model [HS98] of Martin-Löf’s intensional type theory (ITT) [ML75]. Intensional type theory includes the identity type: for every type A and elements M, N ∈ A, there is a type Id_A(M, N) whose elements are proofs that M and N are “equal”. (We henceforth call these elements identities or identifications.) Hofmann and Streicher’s model is designed to falsify the principle of uniqueness of identity proofs, which states that all proofs of a given identity are themselves identical. They thereby show that this principle is, oddly enough, independent of ITT. Far

Key words and phrases: cubical type theory, parametricity, computational type theory, modal type theory.

* This article is an extended version of [CH20].

This material is based on research sponsored by Air Force Office of Scientific Research through MURI grants FA9550-15-1-0053 and FA9550-21-0009 (Tristan Nguyen, program manager). Any opinions, findings and conclusions or recommendations expressed in this material are those of the authors and do not necessarily reflect the views of the AFOSR.

LOGICAL METHODS
IN COMPUTER SCIENCE

DOI:10.46298/LMCS-17(4:5)2021

© E. Cavallo and R. Harper
Creative Commons