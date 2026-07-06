## 5 The Monad-Theory Correspondence

Throughout this section, we fix a locally presentable $\infty$-category $\mathcal{E}$, as well as a *dense, small, full subcategory* $\mathcal{A} \subset \mathcal{E}$.

We write $\mathbf{PreTh}_{\mathcal{A}}$ for the full subcategory of $(\mathbf{Cat}_{\infty})_{\mathcal{A}/}$ of essentially surjective functors $\mathcal{A} \rightarrow \mathcal{K}$ (with $\mathcal{K}$ also being small). Objects of $\mathbf{PreTh}_{\mathcal{A}}$ are called $\mathcal{A}$-pretheories.

**Definition 5.1.** For a $\mathcal{A}$-pretheory $\mathcal{K}$, we define the category of $\mathcal{K}$-models as the pullback:

$$\begin{array}{ccc} \text{Mod}_{\mathcal{E}}(\mathcal{K}) & \longrightarrow & \text{Pr}(\mathcal{K}) \\ \downarrow & \downarrow & \downarrow \\ \mathcal{E} & \longrightarrow & \text{Pr}(\mathcal{A}), \end{array}$$

where the right vertical arrow is the restriction functor and the bottom horizontal arrow is the restricted Yoneda embedding, or “$\mathcal{A}$-nerve” functor. That is, it is the composite of the Yoneda embedding $\mathcal{E} \rightarrow \text{Pr}(\mathcal{E})$ with the restriction to $\mathcal{A} \subset \mathcal{E}$.

**Proposition 5.2.** *The forgetful functor $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \mathcal{E}$ is a monadic right adjoint functor. The functor $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \text{Pr}(\mathcal{K})$ is a fully faithful right adjoint (i.e. is an equivalence to the inclusion of a reflective subcategory).*

*Proof.* The functor $\text{Pr}(\mathcal{K}) \rightarrow \text{Pr}(\mathcal{A})$ is a monadic right adjoint functor. Indeed, it is conservative because $\mathcal{A} \rightarrow \mathcal{K}$ is essentially surjective. It satisfies the condition on split simplicial diagrams because it preserves all colimits and both $\text{Pr}(\mathcal{K})$ and $\text{Pr}(\mathcal{A})$ have all colimits.

Moreover, by Theorem 5.5.3.18 of [15], the above can be seen as a pullback in the category of presentable $\infty$-categories and accessible right adjoint functors, hence the functors $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \mathcal{E}$ and $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \text{Pr}(\mathcal{K})$ are both right adjoint functors.

The monadicity of the first one then follows from Proposition 3.23 and the second one is fully faithful since it is the pullback of $\mathcal{E} \rightarrow \text{Pr}(\mathcal{A})$ which is fully faithful as $\mathcal{A}$ is dense in $\mathcal{E}$. $\square$

**Construction 5.3.** The functoriality of the pullback in Definition 5.1 and the contravariant functoriality of $\mathcal{K} \mapsto \text{Pr}(\mathcal{K})$, make $\text{Mod}_{\mathcal{E}}(-)$ into a functor $\mathbf{PreTh}_{\mathcal{A}}^{op} \rightarrow (\mathbf{Cat}_{\infty})_{/\mathcal{E}}$. By using the identification of 3.22 and taking opposite categories, we obtain a functor:

32