Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:19

the given equations for keys above suffice to derive the two ways of internally stating the interchange laws, viz.

$$\begin{array}{l} \Gamma \operatorname{ctx} @ m \quad \nu_0, \nu_1, \nu_2 : \operatorname{Hom}_{\mathcal{M}}(o, n) \quad \mu_0, \mu_1, \mu_2 : \operatorname{Hom}_{\mathcal{M}}(n, m) \\ \alpha_0 : \mu_0 \Rightarrow \mu_1 \quad \alpha_1 : \mu_1 \Rightarrow \mu_2 \quad \beta_0 : \nu_0 \Rightarrow \nu_1 \quad \beta_1 : \nu_1 \Rightarrow \nu_2 \\ \hline \Gamma \widehat{\mathbf{0}}_{\mu_2 \circ \nu_2} \vdash \widehat{\mathbf{a}}_{\Gamma}^{\alpha_0 \star \beta_0} \circ \widehat{\mathbf{a}}_{\Gamma}^{\alpha_1 \star \beta_1} = \widehat{\mathbf{a}}_{\Gamma}^{\alpha_1 \circ \alpha_0} \widehat{\mathbf{0}}_{\nu_0} \circ \widehat{\mathbf{a}}_{\Gamma \widehat{\mathbf{0}}_{\mu_2}}^{\beta_1 \circ \beta_0} : \Gamma \widehat{\mathbf{0}}_{\mu_0 \circ \nu_0} @ o \end{array}$$

$$\begin{array}{l} \Gamma \operatorname{ctx} @ m \quad \nu_0, \nu_1, \nu_2 : \operatorname{Hom}_{\mathcal{M}}(o, n) \quad \mu_0, \mu_1, \mu_2 : \operatorname{Hom}_{\mathcal{M}}(n, m) \\ \alpha_0 : \mu_0 \Rightarrow \mu_1 \quad \alpha_1 : \mu_1 \Rightarrow \mu_2 \quad \beta_0 : \nu_0 \Rightarrow \nu_1 \quad \beta_1 : \nu_1 \Rightarrow \nu_2 \\ \hline \Gamma \widehat{\mathbf{0}}_{\mu_2 \circ \nu_2} \vdash \widehat{\mathbf{a}}_{\Gamma}^{\alpha_0 \star \beta_0} \circ \widehat{\mathbf{a}}_{\Gamma}^{\alpha_1 \star \beta_1} = \widehat{\mathbf{a}}_{\Gamma \widehat{\mathbf{0}}_{\mu_0}}^{\beta_1 \circ \beta_0} \circ \widehat{\mathbf{a}}_{\Gamma}^{\alpha_1 \circ \alpha_0} \widehat{\mathbf{0}}_{\nu_2} : \Gamma \widehat{\mathbf{0}}_{\mu_0 \circ \nu_0} @ o \end{array}$$

In fact, the second version of the interchange law follows from the first one and the equation that expresses the naturality of $\widehat{\mathbf{a}}_{\Gamma}^{-}$. Conversely, except the two laws for the identity 2-cell and naturality, the given equations follow from either one of the two interchange laws.

While it is no longer necessary to prove that substitution is admissible in the setting of the GAT, we would still like to show that explicit substitutions can be eliminated on closed terms. The proof of canonicity implicitly contains such an algorithm, but that is overkill: a simple, direct argument proves that explicit substitutions can be propagated down to variables. Moreover, we may define the admissible operation mentioned in Section 2 by

$$A^{\alpha} \triangleq A[\widehat{\mathbf{a}}_{\Gamma}^{\alpha}] \quad M^{\alpha} \triangleq M[\widehat{\mathbf{a}}_{\Gamma}^{\alpha}]$$

We may then use the aforementioned algorithm to eliminate the keys.

**Pushing substitutions under modalities.** In order for the aforementioned algorithm to work, we must specify how substitutions commute with the modal connectives of MTT. Unlike previous work [GSB19b], the necessary equations are straightforward:

$$\langle \mu \mid A \rangle[\delta] = \langle \mu \mid A[\delta \widehat{\mathbf{0}}_{\mu}] \rangle \quad \operatorname{mod}_{\mu}(M)[\delta] = \operatorname{mod}_{\mu}(M[\delta \widehat{\mathbf{0}}_{\mu}])$$

This simplicity is not coincidental. Previous modal type theories included rules that, in one way or another, trimmed the context during type checking: some removed variables [Pra65, PD01, Shu18], while others erased context formers, e.g. locks [BCM$^{+}$20, GSB19a]. In either case, it was necessary to show that the trimming operation, which we may write as $\|\Gamma\|$, is functorial: $\Gamma \vdash \delta : \Delta$ should imply $\|\Gamma\| \vdash \|\delta\| : \|\Delta\|$. Unfortunately, the proof of this fact is almost always very complicated. Some type theories avoid it by 'forcing' substitution to be admissible using delayed substitutions [Bd00, LSR17], but this causes serious complications in the equational theory.

MTT circumvents this by avoiding any context trimming. As a result, we need neither delayed substitutions nor a complex proof of admissibility.

## 5. MODELS

In the preceding section we presented the formal definition of MTT in the form of a GAT. As a consequence we automatically obtained a category of models of MTT, as well as (strict) homomorphisms between them [Car78, KKA19]. Moreover, this category of models had an initial object, i.e. the syntax of MTT itself. This category of models is inhabited by algebras for this GAT. Hence, showing that a mathematical structure is a model of MTT becomes a laborious task: one must show that each and every construct can be interpreted