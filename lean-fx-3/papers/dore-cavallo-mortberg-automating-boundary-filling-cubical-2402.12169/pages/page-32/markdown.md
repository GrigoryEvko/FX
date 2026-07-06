28:32

M. DORÉ, E. CAVALLO, AND A. MÖRTBERG

Vol. 22:2

\((p(j \wedge k));\)  
\((i = \mathrm{i}1) \to \mathsf{hfill}(\lambda l \to \lambda \{(j = \mathrm{i}0) \to x; (j = \mathrm{i}1) \to p l\}) (\mathsf{inS}(q j)) k;\)  
\((j = \mathrm{i}0) \to x; (j = \mathrm{i}1) \to p k\})\)  
\((q j)\)

The function hfill  \( \phi t i \)  is used in agda/cubical to define fillers in direction  \( 0 \rightarrow i \) . The term t has to be embedded into the cube structure using inS, which is inserted automatically by the Cubical Agda syntax pretty-printer of the solver.

Using these two automatically constructed proofs, we can readily establish by hand the classical formulation of the Eckmann-Hilton argument in terms of path concatenations:

EckmannHilton :  \( p \cdot q \equiv q \cdot p \) 
EckmannHilton = Sq→Comp p q EckmannHilton-Cube

The boundary problem posed by EckmannHilton can also be passed directly to our solver as a single problem instance (without requiring a manual decomposition into Sq→Comp and EckmannHilton-Cube), and our search strategy should in principle yield a solution to this boundary problem. However, our solver is not yet able to find such a solution within 100s. We have also curated some further boundary problems which cannot be solved at the moment, these include a 7-dimensional analogue of the Square to cube contortion example and the syllepsis [SK22], which establishes a higher coherence property of the Eckmann-Hilton proof.

In summary, while there is room to make the solver more performant, it can quickly prove technical lemmas for us that would be tedious to prove by hand, taking significant proof burden from a user of Cubical Agda. Furthermore, some deeper results of synthetic homotopy theory, like the Eckmann-Hilton argument, can also be proved if the statement is phrased carefully.

## 7. FUTURE AND RELATED WORK

There are many ways in which our work can be extended: the performance of the solver can be improved by exploring other heuristics and refinements of the algorithms; the solver should be properly integrated into theorem provers such as Cubical Agda and redtt. The solver could be extended to problems involving multiple types and functions and to use cubical type theory's transport primitive.

Early work on proof automation in HoTT is Brunerie's work on computer-generated proofs for the monoidal structure of smash products [Bru18] which used path-induction and metaprogramming in Agda. [Grz23] generates visual presentations of Cubical Agda proof terms. The problem of deciding equality in the cofibration logic of cubical type theories has been studied by [RL25]. Among other things, they also establish complexity-related results, in particular, that the entailment problems of the cofibration languages of  \( [ABC^{+}21] \)  and  \( [CCHM18] \)  are coNP-complete. Another line of related work is on higher-dimensional algebraic rewriting, in particular, on  \( \infty \) -categories [FRVR22], operads [TCM19], polygraphs  \( [ABG^{+}25] \)  and associative n-categories [Dor18]. For the latter, the tool homotopy.io [RV21] gives a graphical user interface for constructing cells based on a higher-dimensional generalisation of string diagrams. Recently, there has been work on automatically constructing coherences for globular theories which are “weak” in the sense of having, e.g., unitality and associativity of path concatenation hold not definitionally, but only up to some computational witness (similar to cubical type theory).  \( [BMO^{+}25b] \)  have devised