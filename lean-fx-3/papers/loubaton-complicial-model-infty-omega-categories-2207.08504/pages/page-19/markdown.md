1.1. BASIC CONSTRUCTIONS

and we set

$$\mathrm{M} := \mathrm{M}_{\mathrm{Seg}} \cup \mathrm{M}_{\mathrm{Sat}}.$$

For an integer $n$, we define $\Delta[\Theta_n]$ as the following pushout of category:

$$\begin{array}{c} \{[0]\} \times \Theta_n \longrightarrow \Delta \times \Theta_n \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ 1 \longrightarrow \Delta[\Theta_n] \end{array}$$

and the functor $i$ induces a functor $\Delta[\Theta_n] \to \Theta_{n+1}$. For any $n$, we define

$$\mathrm{M}_n := \mathrm{M} \cap \Delta[\Theta_n].$$

**Definition 1.1.2.17.** Let $C$ be a category and $S$ a set of monomorphisms. A morphism is $f : x \to y$ is $S$-local if it has the unique right lifting property against morphisms of $S$. An object $x$ is $S$-local if $x \to 1$ is $S$-local, or equivalently, if for any $i : a \to b \in S$, the induced functor $\operatorname{Hom}(i, x) : \operatorname{Hom}(b, x) \to \operatorname{Hom}(a, x)$ is an isomorphism.

We can easily check that $S$-local morphisms are stable by composition, left cancellation and pullback. As a consequence, any morphism between $S$-local objects is $S$-local.

**Construction 1.1.2.18.** Let $C$ be a presentable category and $S$ a set of monomorphisms with small codomains. We define $C_S$ as the full subcategory of $C$ composed of $S$-local objects. The theorem 4.1 of [Bou77] implies that $\iota : C_S \to C$ is part of an adjunction

$$\mathbf{F}_S : C \xrightarrow{\iota} C_S : \iota$$

where $\mathbf{F}_S : C \to C_S$ is the localization of $C$ by the smallest class of morphisms containing $S$ and stable under composition and colimit.

**Theorem 1.1.2.19 (Berger).** Let $n \in \mathbb{N} \cup \{\omega\}$. The functor $\operatorname{Psh}(\Theta_n) \to (\infty, n)$-cat defined as the left Kan extension of the canonical inclusion $\Theta \to (\infty, \omega)$-cat induces an isomorphism

$$\operatorname{Psh}(\Theta_n)_{\mathrm{W}_n} \cong (\infty, n)\text{-cat}$$

*Proof.* This is [BSP21, corollary 12.3].

**Remark 1.1.2.20.** Suppose given an other category $D$ fitting in an adjunction

$$F : C \xrightarrow{\iota} D : G$$

with unit $\nu$ and counit $\epsilon$, as well as a set of morphisms $T$ of $D$ such that $F(S) \subset T$. By adjunction property, it implies that for any $T$-local object $d \in D$, $G(d)$ is $S$-local. The previous adjunction induces a derived adjunction

$$\mathbf{L}F : C_S \xrightarrow{\iota} D_T : \mathbf{R}G$$

where $\mathbf{L}F$ is defined by the formula $c \mapsto \mathbf{F}_T F(c)$ and $\mathbf{R}G$ is the restriction of $G$ to $D_T$. The unit is given by $\nu \circ \mathbf{F}_S$ and the counit by the restriction of $\epsilon$ to $D_T$.

19