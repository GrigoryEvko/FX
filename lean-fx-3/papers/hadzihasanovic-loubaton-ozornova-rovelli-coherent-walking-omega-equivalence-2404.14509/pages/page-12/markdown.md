12

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

**Proposition 2.3.** If $\omega Cat_{*,*}^{+}$ denotes the category of bipointed marked $\infty$-categories, there is an adjunction

$$\Sigma: \omega Cat^{+} \rightleftarrows \omega Cat_{*,*}^{+}: \mathrm{hom}$$

Moreover, the functor $\Sigma: \omega Cat^{+} \to \omega Cat^{+}$ preserves connected colimits.

**2.2. The coinductive homotopy theory of marked $\omega$-categories.** We recall that a left semi-model category structure on a category $\mathcal{M}$ consists of three distinguished classes of morphisms of $\mathcal{M}$, called *cofibrations*, *fibrations*, and *weak equivalences*, satisfying a weaker version of the axioms for a model category. We refer the reader to [BW24, Definition 2.1] for a complete list of axioms that these classes must satisfy. An object in $\mathcal{M}$ is said to be *fibrant* if the unique morphism to the terminal object of $\mathcal{M}$ is a fibration, and it is said to be *cofibrant* if the unique morphism from the initial object of $\mathcal{M}$ is a cofibration. The class of *acyclic cofibrations* is the class of morphisms in $\mathcal{M}$ that have the left lifting property with respect to all fibrations between fibrant objects. In a left semi-model structure, the class of acyclic cofibrations is closed under transfinite composition and pushouts and the class of weak equivalences is closed under two-out-of-three.

**Theorem 2.4** ([HL23, §4.2]). There exists a left semi-model structure on $\omega Cat^{+}$, which we denote by $\omega Cat_{\mathrm{coind}}^{+}$ and we call the coinductive left semi-model structure, such that:

(1) a marked $\omega$-functor $f: (\mathcal{D}, t\mathcal{D}) \to (\mathcal{E}, t\mathcal{E})$ is a cofibration in $\omega Cat_{\mathrm{coind}}^{+}$ if and only if the $\omega$-functor $f: \mathcal{D} \to \mathcal{E}$ is a cofibration in $\omega Cat_{\mathrm{can}}$;
(2) a cofibration $f: (\mathcal{D}, t\mathcal{D}) \to (\mathcal{E}, t\mathcal{E})$ between cofibrant objects is a weak equivalence in $\omega Cat_{\mathrm{coind}}^{+}$ if and only if it is an acyclic cofibration, that is, it has the left lifting property against fibrations between fibrants objects;
(3) a marked $\omega$-category $(\mathcal{D}, t\mathcal{D})$ is fibrant in $\omega Cat_{\mathrm{coind}}^{+}$ if and only if $t\mathcal{D} = \mathrm{eq}\,\mathcal{D}$;
(4) a marked $\omega$-functor $f: \mathcal{D}^{\natural} \to \mathcal{E}^{\natural}$ between fibrant objects is a weak equivalence in $\omega Cat_{\mathrm{coind}}^{+}$ if and only the $\omega$-functor $f: \mathcal{D} \to \mathcal{E}$ is a weak equivalence in $\omega Cat_{\mathrm{can}}$;
(5) a marked $\omega$-functor $f: \mathcal{D}^{\natural} \to \mathcal{E}^{\natural}$ between fibrant objects is a fibration in $\omega Cat_{\mathrm{coind}}^{+}$ if and only if it has the right lifting property against the marked $\infty$-functors of the form $i_{n}^{+}: \mathcal{C}_{n}^{\flat} \to (\mathcal{C}_{n+1}, \{e_{n+1}\} \cup \mathrm{id}(\mathcal{C}_{n+1}))$ for all $n \geq 0$. Here, $e_{n+1}$ denotes the non-trivial $(n+1)$-cell of $\mathcal{C}_{n+1}$ and $i_{n}^{+}$ denotes the marked $\omega$-functor that embeds $\mathcal{C}_{n}$ as the codomain of $e_{n+1}$.

*Proof.* The left semi-model structure $\omega Cat_{\mathrm{coind}}^{+}$ is built in [HL23, Definition 4.22] as a left Bousfield localization (in the sense of [BW24, Theorem A]) of the *saturated inductive left semi-model structure* from [HL23, Theorem 3.31]. The saturated inductive left semi-model structure is in turn built as a left Bousfield localization of the *inductive left semi-model structure* from [HL23, Theorem 2.38].

The characterization (1) of cofibrations directly follows from [HL23, Definition 2.27]. The characterization (2) of cofibrations between cofibrant objects that are weak equivalences follows from [Hen20, Proposition 2.2.10]. The characterization (3) of fibrant objects and the characterization (4) of weak equivalences between fibrant objects are in [HL23, Theorem 4.25]. The characterization (5) of fibrations between fibrant objects then directly follows from [HL23, Proposition 3.23], evoking [Hen23, Theorem 7.3(6)] for the fact that a map between fibrant objects in the left Bousfield localization $\omega Cat_{\mathrm{coind}}$ is a fibration if and only if it is one in the inductive left semi-model structure. $\square$