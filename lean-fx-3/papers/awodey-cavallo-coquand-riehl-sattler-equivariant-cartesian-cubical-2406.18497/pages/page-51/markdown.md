4.4. The cubical species model of homotopy type theory. In this section, we apply the results of §3 to verify the type-theoretic properties of the interval premodel structure on cubical species that allow us to show it is a Quillen model structure with the extra features required of a model of homotopy type theory.

The cofibrations in the interval premodel structure are exactly the monomorphisms, which are closed under pushout products in all slices by Remark 2.2.2. Together with Lemma 4.3.19, this verifies the hypotheses of Theorem 3.3.3, and therefore:

Proposition 4.4.1. The interval premodel structure on cubical species satisfies the equivalence extension property. \(\square\)

Similarly, the definition of the fibrations is of the form considered by Proposition 3.4.2, and therefore:

Proposition 4.4.2. The interval premodel structure on cubical species has the Frobenius property. \(\square\)

The remaining properties require universes, which we now construct. By Theorem 4.3.14, the uniform fibrations are determined as a certain pullback of the trivial fibrations. We use this result to define a notion of fibred structure \(\mathbb{F}\) that is locally representable and relatively acyclic and classifies the uniform fibrations.

Lemma 4.4.3. There is a locally representable and relatively acyclic notion of fibred structure \(\mathbb{F}\), the notion of uniform fibration structure, whose underlying class of maps is the class of fibrations.

Proof. We apply Lemma 2.1.16. That is, we define a uniform fibration structure on \( f \colon \mathbb{Y} \to \mathbb{X} \) to be a uniform trivial fibration structure on \( \operatorname{ev} \hat{\circ} f \), the Leibniz pullback application of the evaluation natural transformation

\[
\mathrm{cSet} ^ {\mathbb {E}} \xrightarrow [ \Downarrow \mathrm{ev} ]{(-) ^ {\mathbb {I}} \times \mathbb {I}} \mathrm{cSet} ^ {\mathbb {E}}.
\]

Since the interval \(\mathbb{I}\) is tiny, the functor \(\mathbb{X} \mapsto \mathbb{X}^{\mathbb{I}} \times \mathbb{I}\) has a right adjoint:

\[
\mathrm{cSet} ^ {\mathbb {E}} \xrightarrow [ (-) _ {\mathbb {I}} ]{(-) ^ {\mathbb {I}}} \mathrm{cSet} ^ {\mathbb {E}} \xrightarrow [ (-) ^ {\mathbb {I}} ]{- \times \mathbb {I}} \mathrm{cSet} ^ {\mathbb {E}}.
\]

Since Lemma 2.2.10 tells us that the notion of fibred structure \(\mathbb{T}\mathbb{F}\) is locally representable and relatively acyclic, Lemma 2.1.16 tells us that the same is true for the uniform fibrations.

Instantiating Construction 2.3.3:

Construction 4.4.4. For sufficiently large \(\kappa\), we define a \(\kappa\)-small fibration classifier \(\pi: \dot{\mathbb{U}}_{\kappa} \to \mathbb{U}_{\kappa}\) by defining \(\mathbb{U}_{\kappa} := \mathbb{F}^{\kappa}(\varpi)\) and forming the pullback

\[
\begin{array}{c} \dot {\mathbb {U}} _ {\kappa} \longrightarrow \dot {\mathbb {V}} _ {\kappa} \\ \pi \Big \downarrow^ {\lrcorner} \quad \Big \downarrow^ {\lrcorner} \\ \mathbb {U} _ {\kappa} \xrightarrow [ \psi_ {\varpi} ]{} \mathbb {V} _ {\kappa} \end{array}
\]

where \(\varpi\colon\dot{\mathbb{V}}_{\kappa}\to\mathbb{V}_{\kappa}\) is the Hofmann–Streicher universe classifying \(\kappa\)-small families in the presheaf topos cSet\(^{\mathbb{E}}\).

By Proposition 2.3.5:

51