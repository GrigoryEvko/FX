3.1. PRELIMINARIES

Lemma 3.1.2.12. Let $i: K \to L$ be a monomorphism and $f: X \to Y$ a morphism having the right lifting property against $J$. The induced morphism

$$f^i: X^L \to X^K \times_{Y^K} Y^L$$

has the right lifting property against $J$.

Proof. As the model structure on $\operatorname{Seg}(A)$ is cartesian, $(f^i)^\natural$ is a fibration. We then have to show that this morphism has the right lifting property against $[e, 1]_t \to [e, E^{eq}]^\natural$ and $[e, E^{eq}] \to [e, E^{eq}]^\natural$. We can reduce to the case where $i$ is a generating acyclic cofibration. If $i$ is $\emptyset \to [0]$, this is obvious. We then suppose that $i$ is $[e, 1] \to [e, 1]_t$ or $[a, \partial n] \cup [b, n] \to [b, n]$ for $a \to b$ a generating acyclic cofibration of $A$. In both case, $i$ induces an equivalence on objects. The morphism $i \hat{\times}([e, E^{eq}] \to [e, E^{eq}]^\natural)$ is then the identity. Moreover, $i \hat{\times}([e, 1]_t \to [e, E^{eq}]^\natural)$ fits in the following cocartesian square

$$\begin{array}{c} L^\natural \times [e, 1] \coprod_{K^\natural \times [e, 1]} K^\natural \times ([e, E^{eq}]) \longrightarrow L \times [e, 1]_t \coprod_{K \times [e, 1]_t} K \times [e, E^{eq}]^\natural \\ \downarrow \hspace{2em} \downarrow \\ L^\natural \times [e, E^{eq}] \longrightarrow L \times [e, E^{eq}]^\natural \end{array}$$

The lemma 3.1.2.10 implies $f$ has the right lifting property against the left vertical morphism, and so also against the right vertical one. By adjunction, this implies that $f^i$ has the desired lifting property. $\square$

Theorem 3.1.2.13. There exists a nice model structure on $\operatorname{tSeg}(A)$ where fibrant objects are stratified Segal $A$-categories and weak equivalences between marked Segal $A$-categories are stratified equivalences. The adjunction

$$(\_)^\flat: \operatorname{Seg}(A) \xrightarrow{\perp} \operatorname{tSeg}(A): (\_)^\natural$$

induces a Quillen equivalence.

A left adjoint from $\operatorname{tSeg}(A)$ to a nice model category $C$ is a left Quillen functor if and only if it preserves cofibrations and

(1) for any integer $n$, $[\_, n]: A \to C$ is a left Quillen functor,
(2) for any object $a$ of $A$, $[a, \_]: \operatorname{tPsh}(\Delta) \to C$ sends spine inclusions to weak equivalences,
(3) The morphism $[e, 1]_t \to [0]$ and $[e, E^{eq}] \to [0]$ are sent to weak equivalences.

Proof. We recall that we define $J$ as the union of the set of generating acyclic cofibrations of $\operatorname{Seg}(A)$ and of $\{[e, 1]_t \to [e, E^{eq}]^\natural\}$ and $\{[e, E^{eq}] \to [e, E^{eq}]^\natural\}$ and we suppose that it includes the trivial cofibrations $\{0\} \to [e, E^{eq}]$ and $\{1\} \to [e, E^{eq}]$. We denote by $I$ a cellular model for $\operatorname{Psh}(t\Delta[tB])$.

As $\operatorname{tSeg}(A)$ is the category of $t\Delta[M]$ stratified presheaves on $\Delta[B]$, we have an adjunction

$$\pi: \operatorname{Psh}(t\Delta[tB]) \xrightarrow{\perp} \operatorname{tSeg}(A): \iota$$

where the right adjoint is fully faithful.

The set $l(r(\iota(J)\hat{\times}I))$ is a class of anodyne extensions relative to the interval $\_ \times [e, E^{eq}]$ as defined in [Cis06, paragraph 1.3.12]. We then consider $\operatorname{Psh}(t\Delta[tB])$ endowed with the model structure induced by [Cis06, théorème 1.3.22]. An object is fibrant if and only if it has the right lifting property against $\iota(J)\hat{\times}I$. A morphism between fibrant objects is a fibration if and only if it has the right lifting property against $\iota(J)\hat{\times}I$.

107