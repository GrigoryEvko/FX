Vol. 22:2

AUTOMATING BOUNDARY FILLING IN CUBICAL TYPE THEORIES

28:31

For the remaining side ?₁ we are left to construct a square with the boundary

$$\Gamma \mid j, k \vdash [ j = \mathbf{0} \mapsto r(k) \mid j = \mathbf{1} \mapsto (q \cdot r)(k) \mid k = \mathbf{0} \mapsto q(\sim j) \mid k = \mathbf{1} \mapsto r(\mathbf{1}) ] \text{ bdy}$$

which can be done in much the same spirit as ?₀ was solved.

In summary, having the powerful De Morgan theory at hand makes the proof of associativity of path concatenation relatively straightforward, while already in the case of Dedekind contortions we would have had to come up with additional fillers wherever ∼ was used, let alone the cartesian theory where the solver has to come up with quite involved nested fillers.

### 6. A PRACTICAL SOLVER FOR CUBICAL AGDA BOUNDARY PROBLEMS

We have implemented the solver in Haskell,⁵ providing the first experimental solver for boundary problems coming from Cubical Agda. The implementation of KANCSP is based on a monadic solver for finite domain constraint satisfaction problems [Ove15]. The user inputs problems in a .cube file which contains a cell context and boundary problems over that context. If the solver finds a solution, it is printed in Cubical Agda syntax so that it can be copied and pasted into proof goals. Proper integration into Cubical Agda that allows the solver to be called as a tactic from Agda is left to future work.

We have curated a small benchmarking suite of boundary problems, many of which are from the agda/cubical library. The problems are common proof obligations, such as associativity of path concatenation, rearrangements of sides of cubes, etc. On a standard laptop, all problems are quickly solved (often in < 50ms). This means that the solver is fast enough to fit seamlessly into a formalisation workflow and can be used as a tactic for solving routine proof goals. It can also solve some more complex goals such as Example 5.3.

In Cubical Agda, the constant path at x of type x ≡ x is expressed with λ-abstraction as λ i → x. We can use the PathP type to describe higher-dimensional boundaries, e.g., PathP (λ j → x ≡ x) (λ i → x) (λ i → x) is the boundary of a square with reflexive paths on its sides. Given two such squares p and q, The Eckmann-Hilton cube is derived in ∼150ms:

EckmannHilton-Cube : PathP (λ i → q i ≡ q i) p p

EckmannHilton-Cube = λ i j k → hcomp (λ l → λ {

$$(i = \mathbf{i0}) \to p\,j\,(k \wedge l) ; (j = \mathbf{i0}) \to q\,i\,k ; (k = \mathbf{i0}) \to x ;$$

$$(i = \mathbf{i1}) \to p\,j\,(k \wedge l) ; (j = \mathbf{i1}) \to q\,i\,k ; (k = \mathbf{i1}) \to p\,j\,l \})\,(q\,i\,k)$$

The Cubical Agda primitive hcomp captures Kan fillers in direction 0 → 1. The solution to the boundary problem discussed in the Sq→Comp example is found in ∼15ms, its translation into Cubical Agda looks as follows (manually compressed to not use too much space in the paper; the actual pretty-printed output is more readable):

Sq→Comp : PathP (λ j → q j ≡ q j) p p → p · q ≡ q · p

Sq→Comp α i j = hcomp (λ k → λ {

$$(i = \mathbf{i0}) \to \text{hcomp} \, (\lambda\,l \to \lambda\,$$

$$(j = \mathbf{i0}) \to x ; (k = \mathbf{i0}) \to q\,(j \wedge l) ; (j = \mathbf{i1}) \to \alpha\,l\,k ;$$

$$(k = \mathbf{i1}) \to \text{hfill} \, (\lambda\,m \to \lambda\,\{ (j = \mathbf{i0}) \to x ; (j = \mathbf{i1}) \to q\,m \})\,(\text{inS}(p\,j))\,l \})$$

⁵We have implemented a solver which is parametric over all contortion theories (https://github.com/maxdore/cubetac) as well as a solver specialised to the Dedekind contortions which comes with an interface to Cubical Agda which was used to generate the code in this paper (https://github.com/maxdore/dedekind).