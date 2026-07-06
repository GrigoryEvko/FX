is a pullback square. An $\mathcal{A}$-pretheory $\mathcal{K}$ is said to be an $\mathcal{A}$-theory if $\eta_{\mathcal{K}}$ is an equivalence.

The following then immediately follows from Theorem 5.9 and Remark 2.4:

**Corollary 5.12.** *For any monad $M$, $\mathrm{Th}(M)$ is an $\mathcal{A}$-theory, and for any $\mathcal{A}$-pretheory $\mathcal{K}$, the associated monad $\mu^{\mathcal{K}}$ is $\mathcal{A}$-nervous. Moreover, the monad-theory adjunction restricts to an equivalence between the full subcategories of $\mathcal{A}$-Nervous monads and $\mathcal{A}$-theories.*

## 6 General consequences of the Monad-Theories adjunction

In this section we draw general consequences from the monad-theory adjunction of Theorem 5.9. First, one can use it to construct and study colimits of $\mathcal{A}$-Nervous monads:

**Theorem 6.1.** *Let $\mathcal{E}$ be a presentable $\infty$-category, and let $\mathcal{A} \subset \mathcal{E}$ be a full dense small subcategory. Then the full subcategory of $\mathrm{Mnd}_{\mathcal{E}}$ of $\mathcal{A}$-Nervous monads has all colimits and they are preserved by the inclusion in $\mathrm{Mnd}_{\mathcal{E}}$. Moreover, the contravariant functor sending a monad to its category of algebras preserves these colimits. That is, the natural map:*

$$\mathcal{E}^{\mathrm{Colim}\,M_i} \to \lim_{i \in I} \mathcal{E}^{M_i}$$

*is an equivalence.*

*Proof.* The $\infty$-category of $\mathcal{A}$-pretheories is just the full subcategory of $(\mathrm{Cat}_{\infty})_{\mathcal{A}/}$ of essentially surjective functors, so it has all colimits and they are computed in $(\mathrm{Cat}_{\infty})_{\mathcal{A}/}$. This can be used to compute colimits of $\mathcal{A}$-nervous monads. Indeed, if $(M_i)_{i \in I}$ is a diagram of $\mathcal{A}$-nervous monads, then it induces a diagram $(T_i)_{i \in I}$ of $\mathcal{A}$-theories. The colimit $\mathrm{Colim}\,T_i$ in the $\infty$-category of $\mathcal{A}$-pretheories exists, is preserved by the left adjoint of the monad-theory correspondence and is thus taken by this left adjoint to a colimit of the diagram $(M_i)_{i \in I}$.

The claim about categories of algebras actually holds for general colimits of monads (when they exist) as one can show that every object admits an

37