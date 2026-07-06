STRICT UNIVERSES FOR GROTHENDIECK TOPOI

45

[GB22] proved a canonicity result for a version of guarded dependent type theory for which the necessary instance of STC involved a Grothendieck topology. It has therefore become a matter of some urgency to verify the existence of universes satisfying (U1-8) in arbitrary Grothendieck topoi.

6.3.2. UNIVERSES IN ARTIN GLUINGS. Let $F: \mathcal{E} \longrightarrow \mathcal{F}$ be a left exact functor between topoi such that $\mathcal{E}$ carries the structure of a model of Martin-Löf type theory, i.e. a pre-universe $\mathcal{T}$ in the sense of Definition 1.1.3. Write $\mathcal{G} := \mathcal{F} \downarrow F$ for the Artin gluing of $F$, and let $j: \mathcal{E} \hookrightarrow \mathcal{G}$ be the corresponding open immersion of topoi. Fixing a universe $\mathcal{S}$ in $\mathcal{G}$ (i.e. a class of maps satisfying (U1-7)) that contains $j_*\mathcal{T}$, we may define a new pre-universe $\mathcal{U}$ consisting of the subclass of $\mathcal{S}$ spanned by maps $f$ with $j^*f \in \mathcal{T}$.

We wish to verify that $\mathcal{U}$ likewise carries the structure of a model of Martin-Löf type theory in the same sense of satisfying (U1,3-5); results of this kind are used to prove important syntactic metatheorems for type theories, such as canonicity (a type theoretic analogue to the existence property), normalization, decidability of judgmental equality, and conservativity.

6.3.3. LEMMA. The class of maps $\mathcal{U} \subseteq \operatorname{Hom}_{\mathcal{G}}$ satisfies (U1,3,4).

PROOF. This is a straightforward consequence of the fact that $j^*$ is a logical functor, using the fact that $\mathcal{T}$ and $\mathcal{S}$ satisfy (U1,3,4).

To show that $\mathcal{U}$ is a pre-universe it remains to verify (U5), i.e. show that $\mathcal{U}$ has a generic family. It will turn out that the most elegant way to achieve this factors through an additional assumption that $\mathcal{S}$ satisfies the realignment property (U8).

6.3.4. CONSTRUCTION. We begin by constructing a putative generic family for $\mathcal{U}$ in $\mathcal{G}$, which we will subsequently verify to be generic as an application of the realignment property for $\mathcal{S}$. Because $j_*\mathcal{T} \subseteq \mathcal{S}$, we have in particular a cartesian morphism $j_*\pi_{\mathcal{T}} \longrightarrow \pi_{\mathcal{S}}$ in $\mathcal{G}^\rightarrow$; restricting into the open subtopos, we have $\pi_{\mathcal{T}} \cong j^*j_*\pi_{\mathcal{T}} \longrightarrow j^*\pi_{\mathcal{S}}$ in $\mathcal{E}^\rightarrow$; writing $q: U_{\mathcal{T}} \longrightarrow j^*U_{\mathcal{S}}$ for the base of this morphism, we may define the base of a putative generic family for $\mathcal{U}$ by cartesian lift in the gluing fibration:

$$\begin{array}{c c c} U_{\mathcal{U}} \xrightarrow{\bar{q}} U_{\mathcal{S}} & \mathcal{G} \\ \updownarrow \quad \updownarrow & j^* \\ U_{\mathcal{T}} \xrightarrow{q} j^*U_{\mathcal{S}} & \mathcal{E} \end{array} \tag{44}$$

The remainder of the family is defined by pullback:

$$\begin{array}{c c c} \pi_{\mathcal{U}} \xrightarrow{\quad} \pi_{\mathcal{S}} & \mathcal{G}^\rightarrow \\ \updownarrow \quad \updownarrow & \text{cod} \\ U_{\mathcal{U}} \xrightarrow{\bar{q}} U_{\mathcal{S}} & \mathcal{G} \end{array} \tag{45}$$