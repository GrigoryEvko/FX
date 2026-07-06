4.2.4.1 Declarations and Simple Cases We start by declaring the type of all these structures and operations, and giving those definitions that are direct. First, we will have matching telescopes and matching substitutions:

$$\frac{\gamma^{-} : \pi\Gamma \vdash_{sm^n} A \gamma^{-} \text{type}_\ell}{\gamma_{n+1} : \Gamma_{n+1} \vdash_{dm} A_{\partial(n+1)} \gamma_{n+1} \text{tel}_\ell} \quad \frac{\gamma^{-} : \pi\Gamma \vdash_{sm^n} t \gamma^{-} : A \gamma^{-}}{\gamma_{n+1} : \Gamma_{n+1} \vdash_{dm} t_{\partial(n+1)} \gamma_{n+1} : A_{\partial(n+1)} \gamma_{n+1}}$$

The inductive definitions of these telescopes and substitutions will be given in section 4.2.4.2. However, in terms of them, we are able to define the types and terms of $sm^{n+1}$, as pairs of a type or term in $sm^n$ with a discrete type or term over its matching object. We can formulate these definitions type-theoretically as bidirectional rules.

$$\frac{\gamma^{-} : \pi\Gamma \vdash_{sm^n} \pi A \gamma^{-} \text{type}_\ell}{\gamma_{n+1} : \Gamma_{n+1}, \partial a : \pi A_{\partial(n+1)} \gamma_{n+1} \vdash_{dm} A_{n+1} \gamma_{n+1} \partial a \text{type}_\ell} \quad \frac{\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{type}_\ell}{\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{type}_\ell}$$

$$\frac{\gamma^{-} : \pi\Gamma \vdash_{sm^n} \pi t \gamma^{-} : \pi A \gamma^{-}}{\gamma_{n+1} : \Gamma_{n+1} \vdash_{dm} t_{n+1} \gamma_{n+1} : A_{n+1} \gamma_{n+1} (\pi t_{\partial(n+1)} \gamma_{n+1})} \quad \frac{\gamma : \Gamma \vdash_{sm^{n+1}} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{sm^{n+1}} t \gamma : A \gamma}$$

Extension of contexts by a type $\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{type}_\ell$, and of a substitution by a term $\gamma : \Gamma \vdash_{sm^{n+1}} t \gamma : A \gamma$, are then obtained as follows:

$$\begin{array}{l} (\gamma : \Gamma, a : A \gamma)_{m+1} \equiv (\gamma^{-} : \pi\Gamma, a^{-} : \pi A \gamma^{-})_{m+1} \quad \text{for} \quad m < n \\ (\gamma : \Gamma, a : A \gamma)_{n+1} \equiv (\gamma_{n+1} : \Gamma_{n+1}, \partial a : \pi A_{\partial(n+1)} \gamma_{n+1}, a : A_{n+1} \gamma_{n+1} \partial a) \\ [\sigma, t]_{m+1} \equiv [\pi\sigma, \pi t]_{m+1} \quad \text{for} \quad m < n \\ [\sigma, t]_{n+1} \equiv [\sigma_{n+1}, \pi t_{\partial(n+1)}, t_{n+1}]. \end{array}$$

So far this is just a definition of the family of discrete objects underlying $(\gamma : \Gamma, a : A \gamma)$; we will enhance it to a diagram in (4.15) below.

We will also prove that matching telescopes and substitutions are stable under substitution, such that for $\sigma : \Delta \to \Gamma$ in $\mathcal{C}^{\Delta_{n+1}}$, we have:

$$(A^{\pi\sigma})_{\partial(n+1)} \equiv (A_{\partial(n+1)})^{\sigma_{n+1}} \qquad (t^{\pi\sigma})_{\partial(n+1)} \equiv (t_{\partial(n+1)})^{\sigma_{n+1}}$$

Substitution on types $\gamma : \Gamma \vdash_{sm^{n+1}} A \gamma \text{type}_\ell$ and terms $\gamma : \Gamma \vdash_{sm^{n+1}} t \gamma : A \gamma$ can then be defined as:

$$\begin{array}{l} \pi(A^\sigma) \equiv \pi A^{\pi\sigma} \qquad (A^\sigma)_{n+1} \equiv A_{n+1}^{W_\sigma^{\pi A_{\partial(n+1)}}\sigma_{n+1}} \\ \pi(t^\sigma) \equiv \pi t^{\pi\sigma} \qquad (t^\sigma)_{n+1} \equiv t_{n+1}^{\sigma_{n+1}}. \end{array}$$

Functoriality of substitutions in $sm^{n+1}$ then follows from that of $sm^n$ and $dm$.

In order to define the matching telescopes and substitutions, we will require the definition of display to be part of the mutual induction. As noted above, when working with truncated diagrams, display takes an $(n+1)$-truncated semi-simplicial diagram $A$ to an $n$-truncated one that's dependent on $\pi A$. Since we have no modal locks available yet, we are

54