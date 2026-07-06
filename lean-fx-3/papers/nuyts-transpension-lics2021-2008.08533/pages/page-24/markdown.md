16:24

A. NUYTS AND D. DEVRIESE

Vol. 20:2

## 6. MULTIPLIERS

In this section, we introduce multipliers as a semantics for shapes, as well as the associated modalities $\lrcorner[u] \dashv \forall u \dashv \wr[u]$. In Section 6.1, we define multipliers and a number of criteria by which we can classify them. In Section 6.2, we deal with a technical complication that we dubbed *unpointability*$^{§A}$, which shows up especially in models of guarded and nominal type theory. In Section 6.3, we discuss an extensive number of examples. In Section 6.4, we consider how *copointed*$^{§A}$ multipliers give rise to *shape weakening* modalities that are a special instance of the modalities in Section 5. In Section 6.5, we discuss how a multiplier and its associated operations lift from acting on base and slice categories to acting on categories of elements of semantic shape contexts. Then in Section 6.6, we are finally ready to define the transpension modality and its adjoints and to state the quantification Theorem 6.31 that helps to understand them. In Section 6.7, we say a bit more on cartesian multipliers. In Section 6.8, we briefly list the matters that are not discussed in the current paper but can be found in the technical report [Nuy20b].

**6.1. Shapes and multipliers.** In Section 4, we defined shape contexts as lists of variables and announced that these would be modelled as presheaves over $\mathcal{W}$. Several times, we have hinted at the fact that these shape variables need not satisfy all the usual structural rules (weakening, exchange and contraction). In this section, we make these matters precise.

We associate to each shape $\mathbb{U}$ a functor $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ which extends by left Kan extension to a functor $\sqcup \ltimes \mathbf{y}U : \mathrm{Psh}(\mathcal{W}) \to \mathrm{Psh}(\mathcal{W})$. $^{14}$ We define the semantics of shape contexts $[\sqcup] : \mathrm{ShpCtx} \to \mathrm{Obj}(\mathrm{Psh}(\mathcal{W}))$ as follows:

$$[\cdot] = \top, \qquad [\mathbb{X}, u : \mathbb{U}] = [\mathbb{X}] \ltimes \mathbf{y}U.$$

Of course, if we model shape context extension with $u : \mathbb{U}$ by an *arbitrary* functor, then we will not be able to prove many results. Depending on the properties of the functor, the variable $u$ will obey different structural rules and the $\Phi$-combinator [Mou16, BCM15] (Section 10.2) will or will not be sound for $\mathbb{U}$. For this reason, we introduce some criteria that help us classify shapes. Some of these criteria concern in fact the *fresh weakening functor* for the given multiplier, which is essentially an instance of the following construction:

**Definition 6.1.** Given a functor $F : \mathcal{V} \to \mathcal{W}$ and $V_0 \in \mathrm{Obj}(\mathcal{V})$, we define the action of $F$ on slice objects over $V_0$ as the functor

$$F/V_0 : \mathcal{V}/V_0 \to \mathcal{W}/FV_0 : (V, \varphi) \mapsto (FV, F\varphi).$$

**Definition 6.2.** Assume $\mathcal{W}$ has a terminal object $\top$. A **multiplier** for an object $U$ is an endofunctor$^{15}$ $\sqcup \ltimes U : \mathcal{W} \to \mathcal{W}$ such that $\top \ltimes U \cong U$. This gives us a natural second projection $\pi_2 : (\sqcup \ltimes U) \to U$.

We define the **fresh weakening functor** to the slice category as $\lrcorner_U : \mathcal{W} \to \mathcal{W}/U : W \mapsto (W \ltimes U, \pi_2)$, which is essentially the action of the multiplier on slice objects over $\top$.

We say that a multiplier (as well as its shape) is:

$^{14}$Both $\sqcup \ltimes U$ and $\sqcup \ltimes \mathbf{y}U$ are to be regarded as single-character symbols, i.e. $\ltimes$ in itself is meaningless. In most concrete applications, however, the multiplier is defined as some monoidal product $\sqcup \otimes U$ with a given object $U$, in which case the left Kan extension is naturally isomorphic to Day convolution with $\mathbf{y}U$. For this reason, we also refrain from defining $U := \top \ltimes U$ because we may not have $\top \otimes U = U$ on the nose for the object of interest $U$.

$^{15}$In the technical report [Nuy20b], we generalize beyond endofunctors.