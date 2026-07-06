235

uniqueness rules.

$$\frac{\Gamma.\text{cc.dsc} \gg A \text{ type @ par} \quad \Gamma.\text{cc} \gg P \in \text{Glo}(A) \text{ @ pt}}{\Gamma \gg \text{unmod}(P) \in A \text{ @ par}}$$

$$\frac{\Gamma.\text{cc.dsc} \gg A \text{ type @ par} \quad \Gamma.\text{cc.dsc} \gg M \in A \text{ @ par}}{\Gamma \gg \text{unmod}(\text{mod}(M)) = M \in A \text{ @ par}}$$

$$\frac{\Gamma.\text{dsc} \gg A \text{ type @ par} \quad \Gamma \gg P \in \text{Glo}(A) \text{ @ pt}}{\Gamma \gg P = \text{mod}(\text{unmod}(P)) \in \text{Glo}(A) \text{ @ pt}}$$

We motivate these rules by the following categorical intuition. Per the adjunction between connected components and the discrete embedding, any $\Gamma.\text{cc} \gg P \in \text{Glo}(A) \text{ @ pt}$ corresponds to a term $\Gamma \gg P' \in \text{Disc}(\text{Glo}(A)) \text{ @ par}$. Meanwhile, the adjunction between the discrete embedding and global sections functor provides a counit map $\text{Disc}(\text{Glo}(A)) \to A$ induced by the identity function $\text{Glo}(A) \to \text{Glo}(A)$. The projector unmod is then the composite of these two steps.

We note the similarity between these rules and the rules for the bridge application: $\text{Glo}(A)$ is analogous to $\text{Bridge}(\mathbf{x}, A, M_0, M_1)$, $-\cdot\text{dsc}$ to $(-, \mathbf{x}:\mathbf{I})$, and $-\cdot\text{cc}$ to context restriction $-\setminus -$. In that case, too, we have an adjoint relationship between $-\setminus -$ and $(-, \mathbf{x}:\mathbf{I})$, as discussed in Chapter 11. Definitions of this kind are explored in more generality in [GCKGB21].

**Positive elimination** With the discrete type, on the other hand, we have no further left adjoint upon which to rely. Instead, we formulate a positive elimination rule by introducing a new context former, the modal hypothesis. Recall once more the introduction rule for $\text{Disc}(A)$.

$$\frac{\Gamma.\text{cc} \gg M \in A \text{ @ pt}}{\Gamma \gg \text{mod}(M) \in \text{Disc}(A) \text{ @ par}}$$

Elements of $\text{Disc}(A)$ are elements of $A$ well-typed under $-\cdot\text{cc}$. If we want to inhabit some type family $d: \text{Disc}(A) \gg B$ type, then, it would suffice to show that $B[\text{mod}(a)/d]$ holds given a modal variable $(\text{cc} \mid a: A)$. Such variables range exactly over terms that are well-typed under some modality; we will have the following defining rules for contexts and substitutions.

$$\frac{\Gamma \text{ ctx @ par} \quad \Gamma.\text{cc} \gg A \text{ pretype}}{(\Gamma, (\text{cc} \mid a: A)) \text{ ctx @ par}} \quad \frac{\Gamma' \gg \gamma \in \Gamma \text{ @ par} \quad \Gamma'.\text{cc} \gg M \in A\gamma \text{ @ pt}}{\Gamma' \gg (\gamma, M/a) \in (\Gamma, (\text{cc} \mid a: A)) \text{ @ par}}$$