5:28

E. CAVALLO AND R. HARPER

Vol. 17:4

**Theorem 3.17.** Let $A_0, A_1$ type and $a_0: A_0, a_1: A_1 \gg R$ type be given. If $A_0$ and $A_1$ are bridge-discrete and $Ra_0a_1$ is bridge-discrete for all $a_0, a_1$, then $\mathsf{Gel}_x(A_0, A_1, a_0.a_1.R)$ is bridge-discrete for all $\boldsymbol{x}: \mathbf{I}$.

*Proof.* Abbreviate $G_{\boldsymbol{x}} := \mathsf{Gel}_{\boldsymbol{x}}(A_0, A_1, a_0.a_1.R)$. We show $\mathsf{Path}_{G_{\boldsymbol{x}}}(g, g') \simeq \mathsf{Bridge}_{G_{\boldsymbol{x}}}(g, g')$ for all $\boldsymbol{x}: \mathbf{I}$ and $g, g' \in G_{\boldsymbol{x}}$. Note that when $\boldsymbol{x}$ is an endpoint, this holds by the assumptions that $A_0$ and $A_1$ are bridge-discrete.

We apply extent at $\boldsymbol{x}$, first with $g$ and then with $g'$. It then remains to show that for all $a_0, a_0': A_0, a_1, a_1': A_1$, $q: \mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)$, $q': \mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0', a_1')$, and $\boldsymbol{x}: \mathbf{I}$, we have $\mathsf{Path}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x}) \simeq \mathsf{Bridge}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})$ agreeing with the $\mathsf{loosen}_A$ isomorphism when $\boldsymbol{x} = \mathbf{0}$ and $\mathsf{loosen}_B$ isomorphism when $\boldsymbol{x} = \mathbf{1}$. By Proposition 2.3, it is enough to give an isomorphism

$$\mathsf{Bridge}_{\boldsymbol{x}.\mathsf{Path}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})}(p_0, p_1) \simeq \mathsf{Bridge}_{\boldsymbol{x}.\mathsf{Bridge}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})}(\mathsf{loosen}_{A_0}(p_0), \mathsf{loosen}_{A_1}(p_1))$$

for every $p_0: \mathsf{Path}_{A_0}(a_0, a_0')$ and $p_1: \mathsf{Path}_{A_1}(a_1, a_1')$. By identity elimination (Lemma 1.3), we may assume that $p_0$ and $p_1$ are reflexive paths, in which case (with the help of Remark 3.3) we need to show the following for all $q, q': \mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)$.

$$\mathsf{Bridge}_{\boldsymbol{x}.\mathsf{Path}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})}(\lambda^{\mathbb{I}}...a_0, \lambda^{\mathbb{I}}...a_1) \simeq \mathsf{Bridge}_{\boldsymbol{x}.\mathsf{Bridge}_{G_{\boldsymbol{x}}}(q@\boldsymbol{x}, q'@\boldsymbol{x})}(\lambda^{\mathbf{I}}...a_0, \lambda^{\mathbf{I}}...a_1)$$

Now we flip the binders on either side, leaving us to prove the following.

$$\mathsf{Path}_{\mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)}(q, q') \simeq \mathsf{Bridge}_{\mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)}(q, q')$$

In other words, we need to show that $\mathsf{Bridge}_{\boldsymbol{x}, G_{\boldsymbol{x}}}(a_0, a_1)$ is bridge-discrete; this type is isomorphic to $R$ by relativity, so we are finished by assumption.

**3.3. The law of the excluded middle.** As a corollary to the bridge-discreteness of bool, we can refute the law of the excluded middle for propositions. First, let us introduce a few variations on the excluded middle.

$$\begin{array}{l} \mathsf{LEM}_{\infty} := (A:\mathcal{U}) \to (b: \mathsf{bool}) \times \mathsf{if}_{-\mathcal{U}}(b; A, \neg A) \\ \mathsf{LEM}_{-1} := (A:\mathcal{U}) \to \mathsf{isProp}(A) \to (b: \mathsf{bool}) \times \mathsf{if}_{-\mathcal{U}}(b; A, \neg A) \\ \mathsf{WLEM} := (A:\mathcal{U}) \to (b: \mathsf{bool}) \times \mathsf{if}_{-\mathcal{U}}(b; \neg A, \neg\neg A) \end{array}$$

The *unrestricted excluded middle*, $\mathsf{LEM}_{\infty}$, is already refuted by univalence [Uni13, Corollary 4.2.7]. In short, we can obtain a contradiction by examining the action of $\mathsf{LEM}_{\infty}$ on the negation isomorphism not $\in \mathsf{bool} \simeq \mathsf{bool}$ between bool and itself. In univalent type theory, it is therefore customary to restrict the law to propositions (Definition 1.5). The *excluded middle for propositions*, $\mathsf{LEM}_{-1}$, is validated in the simplicial model of univalent type theory [KL20].

In parametric type theory, however, even this law is refuted. In fact, we can contradict the *weak excluded middle*, WLEM, which applies only to negated types. It follows from function extensionality that negated types are always propositions, so we have $\mathsf{LEM}_{-1} \to \mathsf{WLEM}$.

**Lemma 3.18.** If $A$ type is bridge-discrete, then any function $F \in \mathcal{U} \to A$ is constant.

*Proof.* For any pair of types $B_0, B_1$, we can apply $F$ at the empty relation between them.

$$\lambda^{\mathbf{I}}\boldsymbol{x}.F(\mathsf{Gel}_{\boldsymbol{x}}(B_0, B_1, \dots \perp)) \in \mathsf{Bridge}_A(FB_0, FB_1)$$

When $A$ is bridge-discrete, this induces a path between $FB_0$ and $FB_1$.

□