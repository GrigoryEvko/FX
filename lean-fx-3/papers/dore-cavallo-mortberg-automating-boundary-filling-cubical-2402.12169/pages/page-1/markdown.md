Logical Methods in Computer Science
Volume 22, Issue 2, 2026, pp. 28:1–28:35
https://lmcs.episciences.org/

Submitted Aug. 04, 2025
Published Jun. 15, 2026

# AUTOMATING BOUNDARY FILLING IN CUBICAL TYPE THEORIES

MAXIMILIAN DORÉ, EVAN CAVALLO, AND ANDERS MÖRTBERG

a Department of Computer Science, University of Oxford, United Kingdom
e-mail address: maximilian.dore@cs.ox.ac.uk

b Department of Computer Science and Engineering, University of Gothenburg and Chalmers University of Technology, Sweden
e-mail address: evan.cavallo@gu.se

c Department of Mathematics, Stockholm University, Sweden
e-mail address: anders.mortberg@math.su.se

ABSTRACT. When working in a proof assistant, automation is key to discharging routine proof goals such as equations between algebraic expressions. Homotopy type theory allows the user to reason about higher structures, such as topological spaces, using higher inductive types (HITs) and univalence. Cubical type theory provides computational support for HITs and univalence. A difficulty when working in cubical type theory is dealing with the complex combinatorics of higher structures, an infinite-dimensional generalisation of equational reasoning. To solve these higher-dimensional equations consists in constructing cubes with specified boundaries.

We develop a simplified cubical language in which we isolate and study two automation problems: contortion solving, where we attempt to “contort” a cube to fit a given boundary, and the more general Kan solving, where we search for solutions that involve pasting multiple cubes together. Both problems are difficult in the general case—Kan solving is even undecidable—so we focus on heuristics that perform well on practical examples. Our language encompasses different variations of cubical type theory which differ in their “contortion theory”, i.e., the class of contortions they support. We provide a solver for the contortion problem for the most complex contortion theories currently being researched, namely the Dedekind and De Morgan contortions, by utilising a reformulation of contortions in terms of poset maps. We solve Kan problems using constraint satisfaction programming, which is applicable independently of the underlying contortion theory. We have implemented our algorithms in an experimental Haskell solver that can be used to automatically solve many goals a user of cubical type theory might face. We illustrate this with a case study establishing the Eckmann-Hilton theorem using our solver, as well as various benchmarks—providing the ground for further study of proof automation in cubical type theories.

Key words and phrases: Cubical Type Theory, Automated Reasoning, Constraint Satisfaction Programming.

* This paper is an extended version of Automating Boundary Filling in Cubical Agda [DCM24].

Maximilian Doré was supported by COST Action EuroProofNet, supported by COST (European Co-operation in Science and Technology, www.cost.eu). Evan Cavallo was supported by the Knut and Alice Wallenberg Foundation through the Foundation’s program for mathematics. Anders Mörtberg was supported by the Swedish Research Council (Vetenskapsrådet) under Grant No. 2019-04545.

LOGICAL METHODS
IN COMPUTER SCIENCE

DOI:10.46298/LMCS-22(2:28)2026

© M. Doré, E. Cavallo, and A. Mörtberg
Creative Commons