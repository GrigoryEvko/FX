*Proof.* The proof is similar to the previous lemma. All the definitions and technical results have been established, especially theorem B.25. $\square$

**Corollary B.32.** *There is a natural isomorphism $Id_{\kappa-GAT} \Rightarrow U \circ \mathbb{C}$.*

*Proof.* We have constructed $[\varphi_-]: Id_{\kappa-GAT} \Rightarrow U \circ \mathbb{C}$. $\square$

### B.3.4 The natural isomorphism $\mathbb{C} \circ U \cong Id_{\kappa-CON}$

In this section we aim to construct a natural isomorphism $\eta: Id_{\kappa-CON} \Rightarrow \mathbb{C} \circ U$. Let $\mathcal{C}$ be a $\kappa$-contextual category. For this, we first construct a $\kappa$-contextual functor $\eta_{\mathcal{C}}: \mathcal{C} \rightarrow \mathbb{C}_{U(\mathcal{C})}$. Recall that if $A_\lambda$ is an object in $\mathcal{C}$ then for any $\alpha \leq \lambda$, we denote $p_\alpha: A_\lambda \rightarrow A_\alpha$ as the canonical display map that exists. Then we can make the following definition:

1. For $\eta_{\mathcal{C}}(1) := 1$.
2. If $A_\mu$ is an object with $\mu = \lambda + 1$, then

$$\eta_{\mathcal{C}}(A_\mu) := [\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha \leq \mu}].$$

3. For an object $A_\lambda$, we define $\eta_{\mathcal{C}}(p_0) := \eta_{\mathcal{C}}(p)_0$ where $\eta_{\mathcal{C}}(p)_0: \eta_{\mathcal{C}}(A) \rightarrow 1$.
4. If $A_\lambda, B_\mu$ are non-trivial objects, with $\mu$ a successor ordinal, and $f: A_\lambda \rightarrow B_\mu$ is a morphism in $\mathcal{C}$, then

$$\eta_{\mathcal{C}}(f) := [\langle \overline{p_\beta f}(x_\alpha)_{\alpha < \lambda} \rangle_{\beta \leq \mu}].$$

We observe that if $\mu$ is a limit ordinal, then any map $f: A_\lambda \rightarrow B_\mu$ is determined by a family of maps $\{f_\nu: A_\lambda \rightarrow B_\nu\}_{\nu < \mu}$. Thus, in order to define $\eta$ on such map, it is enough to do it on ordinals $\nu < \mu$ which we can assume to be successor ordinals. The map $\eta(f)$ is the map induced by the family of maps $\{\eta(f_\nu): \eta(A_\lambda) \rightarrow \eta(B_\nu)\}_{\nu < \mu}$. In conclusion, we simply need to prove properties of $\eta$ for successor ordinals; the property for limit ordinals follows using the universal property of the limit object.

**Lemma B.33.** *For any $\mathcal{C}$, $\eta_{\mathcal{C}}: \mathcal{C} \rightarrow \mathbb{C}_{U(\mathcal{C})}$ is a $\kappa$-contextual functor.*

*Proof.* First we verify that it is a functor. Since for any $\alpha < \lambda$ we have $\overline{p_\alpha}(x_\alpha)_{\alpha < \lambda} = x_\alpha$, then it is immediate to see that $\eta_{\mathcal{C}}$ preserves the identities. Assume we have non-trivial morphisms $f: A_\lambda \rightarrow B_\mu$ and $g: B_\mu \rightarrow C_\nu$, then

$$\eta_{\mathcal{C}}(gf) = [\langle \overline{p_\gamma gf}(x_\alpha)_{\alpha < \lambda} \rangle_{\beta \leq \nu}]$$

127