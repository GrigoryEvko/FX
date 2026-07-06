leads to certain limitations, e.g. without symmetry it is unclear how to give a corecursion principle for SST$^{d}$.

It should be possible to formulate a version of dTT (unary or higher-ary) with symmetry, but in the presence of symmetry it is unclear whether it is possible for display to compute definitionally on type-formers. However, it should work to use either the interval-based style of [BM12, BCM15, Mou16] or the 'observational' style of [ACKS24].

5.0.0.8 Unimode dTT. We have formulated dTT with two modes, but intuitively the discrete mode is unnecessary, as the dm-types are embedded in the sm-types by the modality $\triangle$. Thus, it should be possible to formulate a version of dTT in which there is only one mode. This is similar to other situations such as spatial/cohesive type theory [Shu18] and synthetic guarded domain theory [GKNB21] that have both unimodal and bimodal versions.

5.0.0.9 Conjectural syntax. In addition to displayed coinductive types, one may consider other kinds of generalized inductive and coinductive types. These are especially useful when taking a more 'synthetic' approach to higher structures in dTT, using the sm-types as augmented semi-simplicial objects rather than working with the internally defined type SST of semi-simplicial types.

Firstly, regarding display as analogous to paths in homotopy type theory suggests displayed inductive types as analogues of higher inductive types. Here the constructors generate displayed elements rather than ordinary ones. As an example, we can construct the simplicial cone of any type:

data C (A : $\square$ Type) : Type where
  $\iota$ : A $\to$ C A
  $\sigma$ : (x : A) $\to$ (C A)$^{d}$ ( $\iota$ x)

f : C A $\to$ B
f ( $\iota$ x) = ?$_{\iota}$ : B
f$^{d}$ ( $\iota$ x) ( $\sigma$ x) = ?$_{\sigma}$ : B$^{d}$ ?$_{\iota}$

Secondly, regarding both display and paths as a kind of modality suggests considering more general modal inductive types, whose constructors can land in modal versions of the type. For instance, since $\diamond A$ is the (-1)-simplices of A, a $\diamond$-modal constructor adds a (-1)-simplex without any higher simplices above it. In this way we can construct the free-living (-1)-simplex, and then all the higher simplices by coning:

data $\Delta^{-1}$ : Type where
  $\star$ : $\diamond$ $\Delta^{-1}$

f : $\Delta^{-1}$ $\to$ A
$\diamond$ f $\star$ = ?$_{\star}$ : $\diamond$ A

$\Delta$ : N $\to$ Type
$\Delta$ zero = C $\Delta^{-1}$
$\Delta$ (suc n) = C ($\Delta$ n)

Note that in both cases, we rely on the computation behaviour of $^{d}$ and $\diamond$ in order to directly give induction principles.$^{10}$ For example, the pattern match $\diamond$ f $\alpha$ requires that $\diamond$

$^{10}$The case splits for defining a function f valued out of an inductive type in this hypothetical extension of Agda,

99