1. If $\Phi = \top$, then $\Phi(x)$ is true and if $\Phi = \bot$ then $\Phi(x)$ is false,
2. If $\Phi = \neg\Psi$, then $\Phi(x)$ is true if and only if $\Psi(x)$ is false,
3. If $\Phi = \bigvee \Phi_i$, then $\Phi(x)$ is true if and only if $\Phi_i(x)$ is true for some $i$,
4. If $\Phi = \bigwedge \Phi_i$, then $\Phi(x)$ is true if and only $\Phi_i(x)$ is true for all $i$,
5. If $\Phi = \exists\{x_\beta : \Gamma_\beta\}_{\gamma \in \beta < \alpha} \Psi$ for $\Gamma' = \left( \Gamma, \{x_\beta : \Gamma'_\beta\}_{\gamma \in \beta < \alpha} \right)$ a context extension, with $p : \Gamma' \to \Gamma$ the corresponding generalized display map, then $\Phi(x)$ is true if there exists a $y \in X(\Gamma')$ such that $p(y) = x$ and $\Psi(y)$,
6. If $\Phi = \forall\{x_\beta : \Gamma_\beta\}_{\gamma \in \beta < \alpha} \Psi$ in the same situation as above, then $\Phi(x)$ is true if for any $y \in X(\Gamma')$ such that $p(y) = x$ we have $\Psi(y)$.

The following lemma is immediate by induction, the proof is left to the reader.

**Lemma 2.9.** *Let $X$ be a model of a generalized $\kappa$-algebraic theory $T$.*

1. *For $\Phi, \Psi \in \mathcal{L}^T_\lambda(\Gamma)$ and $x \in X(\Gamma)$, then if $\Psi \vdash_\Gamma \Phi$ and $\Psi(x)$ then $\Phi(x)$.*
2. *If $f : \Gamma \to \Delta$ is any context morphism and $\Phi = f^*\Psi$ and $x \in X(\Gamma)$ then $\Phi(x) \Leftrightarrow \Psi(f(x))$.*

**Definition 2.10.** We write $\Psi \dashv_\Gamma \Phi$ to mean both $\Psi \vdash_\Gamma \Phi$ and $\Phi \vdash_\Gamma \Psi$. We denote by

$$\mathbb{L}^T_\lambda(\Gamma) := \mathcal{L}^T_\lambda(\Gamma) / (\dashv_\Gamma)$$

the quotient.

Note that $(\dashv_\Gamma)$ is indeed an equivalence relation, as $\vdash_\Gamma$ is transitive and reflexive.

*Remark 2.11.* It follows from theorem 2.7 that for a context morphism $f : \Delta \to \Gamma$ the $f^*$ operation from $\mathcal{L}^T_\lambda(\Gamma) \to \mathcal{L}^T_\lambda(\Delta)$ is compatible with the relation $\dashv$, and hence it descends to an operation

$$f^* : \mathbb{L}^T_\lambda(\Gamma) \to \mathbb{L}^T_\lambda(\Delta).$$

It is also easy to see from theorem 2.6 that the relation $\vdash$ is compatible with all the logical operations on $\mathcal{L}^T_\lambda$, that is $\neg, \bigvee, \bigwedge, \exists, \forall$ in the sense that for example, if $\Phi_i \vdash \Psi_i$ for all $i \in I$ then $\bigvee_{i \in I} \Phi_i \vdash \bigvee_{i \in I} \Psi_i$ and hence they all descend into operations on $\mathbb{L}^T_\lambda$.

13