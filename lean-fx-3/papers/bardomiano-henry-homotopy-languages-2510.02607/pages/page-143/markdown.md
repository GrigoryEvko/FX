Furthermore, a morphism between $\kappa$-coclans $F : \mathcal{C} \to \mathcal{E}$ is an equivalence of $\kappa$-coclans if there exists another morphism of $\kappa$-coclans $G : \mathcal{E} \to \mathcal{C}$ and natural isomorphisms $GF \cong Id_{\mathcal{C}}$ and $FG \cong Id_{\mathcal{E}}$.

Similarly, $F : \mathcal{C} \to \mathcal{E}$ is a morphism of $\kappa$-clans simply if $F^{op} : \mathcal{C}^{op} \to \mathcal{E}^{op}$ morphism of $\kappa$-coclans, and an equivalence of $\kappa$-clans if $F^{op} : \mathcal{C}^{op} \to \mathcal{E}^{op}$ is an equivalence $\kappa$-coclans.

**Proposition B.61.** A morphism of clans $F : \mathcal{C} \to \mathcal{E}$ is an equivalence of clans if and only if $F$ reflects fibrations and transfinite compositions in $Dis(\mathcal{E})$; that is, if $F(Lim_{\lambda}A_{\alpha}) \twoheadrightarrow F(A_0)$ is the transfinite composition of the sequence

$$F(Lim_{\lambda}A_{\alpha}) \cdots \twoheadrightarrow FA_2 \twoheadrightarrow FA_1 \twoheadrightarrow FA_0$$

then $Lim_{\lambda}A_{\alpha} \twoheadrightarrow A_0$ is the transfinite composition of the sequence

$$\cdots \twoheadrightarrow A_2 \twoheadrightarrow A_1 \twoheadrightarrow A_0.$$

The equivalence of theorem B.57 give us an equivalence between clans.

**Corollary B.62.** For any $\kappa$-coclan $\mathcal{C}$ there exists a $\kappa$-contextual category equivalent to it.

Proof. Let us take the $\kappa$-clan given by $\mathcal{D} := \mathcal{C}^{op}$. We can then observe that $\mathcal{D} \cong \mathcal{D}(1)$, where $\mathcal{D}(1)$ is the $\kappa$-contextual category obtained from theorem B.60. We can take the opposites again to get $\mathcal{C}$. $\square$

### C Weak model categories

The most general setting in which we will show good homotopy-theoretic properties of the language introduced in section 2 is the framework of weak model categories introduced in [Hen20], which we will briefly recall here. In practice this extra generality compared to a Quillen model structure is not extremely useful — all the examples we will consider in section 3 are Quillen model structures — so it would not be unreasonable to skip the present subsection. There are two reasons why we need weak model categories:

- A key construction toward the proof of the third invariance theorem in section 4 is in general only a weak model structure, and we need to use its language as an intermediate tool.
- Future applications to left and right semi-model structures — actual weak model structure that are not left or right semi-model structures — are fairly uncommon, but the weak model categories which include both left and right semi-model structure at the same time, are considerably more common.

143