$$\begin{array}{rcl} \mathbf{PreTh}_{\mathcal{A}} & \to & \mathbf{Mnd}_{\mathcal{E}} \\ \mathcal{K} & \mapsto & \mu^{\mathcal{K}}, \end{array}$$

which is characterized by the natural isomorphism $\mathcal{E}^{\mu^{\mathcal{K}}} \simeq \mathrm{Mod}_{\mathcal{E}}(\mathcal{K})$.

**Lemma 5.4.** *There is a functor $(\mathbf{Cat}_{\infty})_{\mathcal{A}/} \to \mathbf{PreTh}_{\mathcal{A}}$ which takes each arrow $\mathcal{A} \to \mathcal{X}$ to its essential image $\mathcal{A} \to \mathcal{Y} \subset \mathcal{X}$.*

*Proof.* We claim that in $\mathbf{Cat}_{\infty}$ essentially surjective functors and fully faithful functors form an orthogonal factorization system (in the sense of [15, Definition 5.2.8.8]). The result then follows from [15, Lemma 5.5.8.19].

Indeed, this is just the (-1)-connected case of the n-connected/n-truncated factorization which exists in any locally presentable $\infty$-category by Proposition 4.6 of [9]. $\mathbf{Cat}_{\infty}$ can be presented as the simplicial category of bifibrant objects of the variant of the Joyal model structure on marked simplicial sets (from [15, Proposition 3.1.3.7] in the special case where $S = \Delta[0]$), which is a simplicial combinatorial model category, so $\mathbf{Cat}_{\infty}$ is a locally presentable $\infty$-category by [15, Theorem A.3.7.6], and the factorization system exists. $\square$

**Definition 5.5.** Let $\mathrm{Th}: \mathbf{Mnd}_{\mathcal{E}} \to \mathbf{PreTh}_{\mathcal{A}}$ be the composite

$$\mathbf{Mnd}_{\mathcal{E}} \xrightarrow{\mathcal{E}_{\bullet}} (\mathbf{Cat}_{\infty})_{\mathcal{E}/} \xrightarrow{(-)\circ i} (\mathbf{Cat}_{\infty})_{\mathcal{A}/} \to \mathbf{PreTh}_{\mathcal{A}}$$

where the first functor is the Kleisli category functor constructed in Corollary 4.6 and the last functor is the functor from 5.4 that takes the fullyfaithful-essentially surjective factorization.

As shown in 2.2, to produce an adjunction of $\infty$-categories, it suffices to produce a counit and unit transformation, and verify the triangle identities on components. We will apply this strategy to show that $\mu^{(-)} \dashv \mathrm{Th}$.

**Construction 5.6.** Consider the commutative square from Definition 5.1. By taking the left adjoint of each functor, we get a commutative diagram in $(\mathrm{Cat}_{\infty})$:

$$\begin{array}{c} \mathcal{E}^{\mu^{\mathcal{K}}} \xleftarrow{\quad} \mathrm{Pr}(\mathcal{K}) \xleftarrow{y_{\mathcal{K}}} \mathcal{K} \\ \uparrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathcal{E} \xleftarrow{\quad} \mathrm{Pr}(\mathcal{A}). \end{array} \tag{4}$$

33