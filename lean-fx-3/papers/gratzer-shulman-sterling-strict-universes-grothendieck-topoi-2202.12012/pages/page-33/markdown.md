STRICT UNIVERSES FOR GROTHENDIECK TOPOI

33

Given a poset $(I, \leq)$ and conservative functor $\lambda \colon I \to {}^{\kappa/}\mathbf{Card}$ of strongly inaccessible cardinals, these results extend to a hierarchy of universes indexed in $I$:

4.4.3. COROLLARY. *Each universe $S_{\lambda_i}$ satisfies (U1–8) and for each $i < j$, there is a cartesian monomorphism $\pi_{\lambda_i} \hookrightarrow \pi_{\lambda_j}$ and $\operatorname{cod}(\pi_{\lambda_i})$ is $\lambda_j$-compact.*

## 5. Relating internal formulations of realignment

We have focused on the external formulation of realignment as a property of a class of maps; recent years have seen several applications of type-theoretic formulation of realignment that employs the internal language of a topos. In Section 5.1 we discuss a logical formulation popularized by Orton and Pitts, which we compare with a more geometrical formulation due to Sterling in Section 5.2 that mirrors the recollement of a space from open and closed subspaces, completing the latent analogy with Artin gluing.

5.1. INTERNAL REALIGNMENT À LA ORTON AND PITTS. In another guise, Cohen, Coquand, Huber, and Mörtberg [Coh+17] has employed the realignment property in the cubical set model of cubical type theory, later rephrased into the internal language of topoi by Birkedal, Bizjak, Clouston, Grathwohl, Spitters, and Vezzosi [Bir+16] and employed by Orton and Pitts [OP16] to give more abstract and general constructions of models of cubical type theory in presheaf topoi.

In what follows, we fix a universe $\mathcal{S}$ satisfying (U1–5) such that, in particular, there is a generic map $\pi \colon E \to U$ for $\mathcal{S}$. We recall the internal version of the realignment axiom for $U$ below as presented by Orton and Pitts [OP16, Axiom 9 $(\mathsf{ax}_9)$], using informal type theoretic notations.

5.1.1. NOTATION. For any $B : U$, an *isomorph* of $B$ is defined to be a type $A : U$ together with an isomorphism $f : A \cong B$. We will write $\operatorname{Iso}_{\mathcal{S}}(B) := \sum_{A:U} A \cong B$ for the type of isomorphs of $B$, and $\operatorname{Iso}_{\mathcal{S}} := \sum_{B:U} \operatorname{Iso}_{\mathcal{S}}(B)$ for the object of isomorphisms.

5.1.2. NOTATION. We will write $X^+$ for the partial map classifier $\sum_{\phi: \Omega} X^\phi$, and $\eta^+ : X \to X^+$ for its unit.

5.1.3. DEFINITION. *A realignment structure is defined to be an element of the dependent type $\prod_{B:U} \prod_{A: \operatorname{Iso}_{\mathcal{S}}(B)^+} \{G : \operatorname{Iso}_{\mathcal{S}}(B) \mid A \downarrow \to A = \eta^+(G)\}$. The realignment axiom on $U$ postulates the existence of a realignment structure.*

Combining the application described in Section 6.3 with the internal perspective of Orton and Pitts [OP16], the realignment operation is included as an axiom of *synthetic Tait computability* [Ste21], the mathematical framework behind the recent normalization result for cubical type theory [SA21].

We demonstrate in Lemmas 5.1.5 and 5.1.6 that the existence of realignment structures in the sense of Definition 5.1.3 is equivalent to the realignment property of Definition 1.1.4.