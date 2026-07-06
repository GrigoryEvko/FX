Note that these computation rules were exactly obtained by applying display to both sides of the equation in the initial computation rules. We can iterate this to obtain:

$$Z^{d^n} \left( (R_T \bar{Z} \bar{S})^{d^n} \sigma^n \right) \partial a \equiv \bar{Z}^{d^n} \sigma^n \partial a$$

$$S^{d^n} \left( (R_T \bar{Z} \bar{S})^{d^n} \sigma^n \right) \partial a \, a \equiv (R_T \bar{Z} \bar{S})^{d^{n+1}} \langle \sigma^n, \bar{S}^{D^n} \sigma^n \partial a \, a \rangle$$

The situation on our hands is not unlike that of Agda, where a definition of f made by (co)pattern matching defines a new normal form and does not expand to a first class intro or elim form when normalised⁶; such names only reduce when their defining patterns occur. This specific point does not itself inhibit Nat canonicity (which Cubical Agda otherwise currently lacks due to its treatment of transport in indexed inductives).

We conjecture that dTT, including its treatment of SST, is fully computational in the sense of Nat canonicity, normalization, and decidable typechecking. More precisely, although this may very well not hold verbatim of the theory as written down in this paper, we expect it to hold of a modified presentation fitting within the general framework of ideas. In particular, while we have presented dTT only as a Generalised Algebraic Theory, all the equations have a clear direction and there are no obvious stuck terms.

### 3.2 EXAMPLES OF SEMI-SIMPLICIAL TYPES

Of course, simply defining a type of semi-simplicial types is only the first step: we also want to be able to work with such things conveniently. Developing a full theory of semi-simplicial types is beyond the scope of this paper, but in this section we will give a few examples to suggest that this at least may be possible with our definition of SST and its corecursion principle. We will use Agda-esque copattern-matching, and assume that our type theory has plenty of other structure rather than the bare-bones version of dTT that we have studied formally in this paper.

### 3.2.1 The singular semi-simplicial types

Thus far we have not discussed propositional equality at all, and the reason for this is that the implementation of display is independent from any implementation of equality, whether that be Martin-Löf, cubical, or observational. However, we now want to define a semi-simplicial type that arises from the ∞-groupoid structure of a type in HoTT. For concreteness we will do this using a cubical notion of equality, with notation that aligns with Cubical Agda.

When dTT is combined with cubical type theory, we expect display on cubical path types should work as follows. We have:

$$A : \text{Type}_\ell, x : A, y : A \vdash_{\text{sm}} \text{Path } A \times y \text{ type}_\ell$$

$$A : \text{Type}_\ell, P : A \to \text{Type}_\ell, x : A, x' : P \times,$$

$$y : A, y' : P \times, p : \text{Path } A \times y \vdash_{\text{sm}} \text{PathP } (\lambda \text{ i. } P \text{ (p i)}) \times' y' \text{ type}_\ell,$$

⁶The culprit here is not a lack of first-class forms, since Agda has pattern matching lambdas. Rather, the restriction is made primarily to control such runaway unfolding that would substantially affect the performance of type-checking and normalisation. As a consequence, two structurally identical top-level definitions of functions f and g made by pattern matching are not definitionally equal.

32