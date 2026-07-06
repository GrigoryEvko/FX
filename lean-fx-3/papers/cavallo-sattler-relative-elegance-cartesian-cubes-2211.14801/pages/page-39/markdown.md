Relative Elegance and Cartesian Cubes with One Connection

39

## 5 Relatively elegant Reedy categories

To show that the adjunction $\blacktriangle_{\cdot} \dashv \blacktriangle^{*}$ defined in Section 4.4 is a Quillen equivalence, it remains to check that its counit is valued in weak equivalences, that is, that $\varepsilon_X: \blacktriangle_{\cdot}\blacktriangle^{*}X \to X$ is a weak equivalence for every fibrant $X \in \mathrm{PSh}(\overline{\square}_{\vee})$. We noted earlier (Proposition 2.20) that for an elegant Reedy category $\mathbf{R}$, we have a convenient set of objects—the automorphism quotients of representables—that generate the whole of $\mathrm{PSh}(\mathbf{R})$ upon saturation by monomorphisms. We will see later on (Corollary 7.3) that the class of $X \in \mathrm{PSh}(\overline{\square}_{\vee})$ for which $\varepsilon_X$ is a weak equivalence is saturated by monomorphisms, so if $\overline{\square}_{\vee}$ were an elegant Reedy category we would have a line of attack. Unfortunately, this is not the case. Indeed, $\overline{\square}_{\vee}$ is not a Reedy category at all (Proposition A.1).

We therefore require a generalization of elegant Reedy theory. We consider categories $\mathbf{C}$ equipped with a fully faithful functor $i: \mathbf{C} \to \mathbf{R}$ into a Reedy category $\mathbf{R}$ that has pushouts of lowering spans and is elegant relative to $i$: such that $N_i := i^* \nmid: \mathbf{R} \to \mathrm{PSh}(\mathbf{C})$ preserves lowering pushouts. In this case, the objects of $\mathrm{PSh}(\mathbf{C})$ are generated upon saturation by monos from the set of automorphism quotients of objects in the image of $N_i$. When $i = \mathrm{id}$, we recover the original theorem for elegant Reedy categories. In Section 6, we shall see that $\overline{\square}_{\vee}$ embeds elegantly in the category of inhabited finite semilattices.

In Section 5.1, we review Reedy monomorphisms and the construction of cellular presentations for maps between presheaves over a Reedy category. In Section 5.2, we narrow our focus to what we call pre-elegant Reedy categories, those having pushouts of lowering spans. The Reedy monic presheaves are in this case characterized as those sending lowering pushouts to pullbacks. This sets the stage for Section 5.3, where we define and study elegance relative to an embedding $i: \mathbf{C} \to \mathbf{R}$.

### 5.1 Cellular presentations and Reedy monomorphisms

For the theory of cellular presentations of diagrams over Reedy categories, we follow Riehl and Verity [RV14; Rie17]. Almost none of the content in this section is novel. For simplicity, we restrict our attention throughout to presheaves, though much of the theory generalizes to functors from a Reedy category into any category.

#### 5.1.1 Weighted colimits

Riehl and Verity observe that many arguments in Reedy category theory are naturally phrased in terms of weighted (col)imits. While more fundamental to enriched category theory, these can have a clarifying role even in ordinary (i.e., Set-enriched) category theory.

Definition 5.1 Let $\mathbf{E}$ be a category. Let a functor $W: \mathbf{C}^{\mathrm{op}} \to \mathbf{Set}$ (the weight) and a diagram $F: \mathbf{C} \to \mathbf{E}$ be given. A weighted colimit for this data is an object $W \circledast_{\mathbf{C}} F \in \mathbf{E}$, equipped with a natural transformation $W \to \mathbf{E}(F-, W \circledast_{\mathbf{C}} F)$, such that for any $X \in \mathbf{E}$ the induced map

$$\mathbf{E}(W \circledast_{\mathbf{C}} F, X) \to [\mathbf{C}^{\mathrm{op}}, \mathbf{Set}](W, \mathbf{E}(F-, X))$$

2025/10/16 00:43