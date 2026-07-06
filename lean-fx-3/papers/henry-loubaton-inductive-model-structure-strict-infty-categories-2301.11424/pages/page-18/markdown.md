and $f \hat{\ominus} g$ is the canonical morphism

$$X \ominus B \coprod_{X \ominus A} Y \ominus A \rightarrow Y \ominus B$$

We refer to the appendix of [29] for the general theory of pushout products and their formal properties.

**2.36 Proposition.** *If $f$ and $g$ are two cofibrations in $\infty$-Cat$^{+m}$, then $f \hat{\ominus} g$ and $f \hat{\ominus} g$ are both cofibrations.*

*Proof.* By the usual properties of the corner-product, it is enough to check this when $f$ and $g$ are generating cofibrations. If $f$ and $g$ are both in $I^\partial$, then $f \ominus g$ has no marked arrows in either its domain or codomain and coincides with the corner-product $f \hat{\otimes} g$ in $\infty$-Cat, which is a cofibration by [5, theorem 3.9]. $f \ominus g$ is the same except that some arrows are marked, but we can always add these markings by taking additional pushouts by morphisms in $I^{+m}$, so it is again a cofibration.

The forgetful functor $\infty$-Cat$^{+m}$ $\rightarrow \infty$-Cat is monoidal for both tensor products and preserves colimits, so it preserves the corner-product. In particular, if either $f$ or $g$ is in $I^{+m}$, then it is sent to isomorphisms by this forgetful functor, and hence $f \hat{\ominus} g$ and $f \hat{\ominus} g$ induce isomorphisms between their underlying $\infty$-categories. Now, if $f: (X, N) \rightarrow (X, M)$ is a morphism in $\infty$-Cat$^{+m}$ that induces an isomorphism on underlying $\infty$-categories, then it is a pushout of morphisms in $I^{+m}$: one simply needs to take such pushouts to make all arrows in $M$ marked. □

**2.37 Construction.** We define $I := \mathbb{D}_1^2 = (\mathbb{D}_1, \{e_1\})$. It is the $\infty$-category with two objects, $e_0^-$ and $e_0^+$, and a marked arrow $e_1: e_0^- \rightarrow e_0^+$. We denote by $j_-$ and $j_+$ the two maps $\mathbb{D}_0 \rightarrow I$ corresponding, respectively, to the two objects $e_0^-$ and $e_0^+$. This gives a diagram:

$$\mathbb{D}_0 \coprod \mathbb{D}_0 \mapsto I \rightarrow \mathbb{D}_0$$

which will play the role of the interval object for our left semi-model structure on $\infty$-Cat$^{+m}$.

We will take as a set of “generating anodyne cofibrations” (also called a “pseudo-generating set of acyclic cofibrations”) the set of maps of the form $j_+ \hat{\ominus} i$ where $i$ is a generating cofibration, more precisely:

**2.38 Definition.**

- We say that a morphism is a *generating anodyne cofibration* if it is of the form $j_+ \hat{\ominus} i$ with $i$ a generating cofibration.
- We say that a morphism in $\infty$-Cat$^{+m}$ is a *naive fibration* if it has the right lifting property against all morphisms of the form $j_+ \hat{\ominus} i$, where $j_+: \mathbb{D}_0 \rightarrow I$ is as in Construction 2.37, and $i$ is one of the generating cofibrations as in Definition 2.32.
- We say that an $m$-marked $\infty$-category $C$ is *fibrant* if the morphism $C \rightarrow 1$ is a naive fibration.
- We say that a morphism in $\infty$-Cat$^{+m}$ is an *anodyne cofibration* if it has the right lifting property against all naive fibrations.

18