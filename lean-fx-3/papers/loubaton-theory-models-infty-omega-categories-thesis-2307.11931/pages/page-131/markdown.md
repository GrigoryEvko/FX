3.1. PRELIMINARIES

induced by $[a, d^0]$ and $[a, d^2]$ are weak equivalences. In particular, this implies that the canonical morphism from the pushout of the span of (3.1.2.8) to $[a, 1]$ is a weak equivalence. As the upper horizontal vertical morphisms of (3.1.2.8) is a cofibration, this implies that this square is homotopy cocartesian which concludes the proof. □

**Lemma 3.1.2.9.** *Let $i: K \to L$ be a monomorphism and $f: X \to Y$ a morphism having the right lifting property against $J$. The induced morphism*

$$f^i: X^L \to X^K \times_{Y^K} Y^L$$

*has the right lifting property against $J$.*

*Proof.* As the model structure on $\operatorname{Seg}(A)$ is cartesian, $(f^i)^\natural$ is a fibration. We then have to show that this morphism has the right lifting property against $[e, 1]_t \to (E^\cong)'$ and $E^\cong \to (E^\cong)'$. We can reduce to the case where $i$ is a generating acyclic cofibration. If $i$ is $\emptyset \to [0]$, this is obvious. We then suppose that $i$ is $[e, 1] \to [e, 1]_t$ or $[a, \partial n] \cup [b, n] \to [b, n]$ for $a \to b$ a generating acyclic cofibration of $A$. In both case, $i$ induces an equivalence on objects. The morphism $i \hat{\times} (E^\cong \to (E^\cong)')$ is then the identity. Moreover, $i \hat{\times} ([e, 1]_t \to (E^\cong)')$ fits in the following cocartesian square

$$\begin{array}{ccc} L^\natural \times [e, 1] \coprod_{K^\natural \times [e, 1]} K^\natural \times (E^\cong) & \longrightarrow & L \times [e, 1]_t \coprod_{K \times [e, 1]_t} K \times (E^\cong)' \\ \downarrow & & \downarrow \\ L^\natural \times E^\cong & \longrightarrow & L \times (E^\cong)' \end{array}$$

The lemma 3.1.2.7 implies $f$ has the right lifting property against the left vertical morphism, and so also against the right vertical one. By adjunction, this implies that $f^i$ has the desired lifting property. □

**Proposition 3.1.2.10.** *There exists a nice model structure on $\operatorname{tSeg}(A)$ where fibrant objects are stratified Segal $A$-categories and weak equivalences between marked Segal $A$-categories are stratified equivalences. The adjunction*

$$(\_)^\flat: \operatorname{Seg}(A) \xrightarrow{\perp} \operatorname{tSeg}(A): (\_)^\natural$$

*induces a Quillen equivalence.*

*A left adjoint from $\operatorname{tSeg}(A)$ to a model category $C$ is a left Quillen functor if it preserves cofibrations, and sends elementary anodyne extensions and morphisms $[e, 1]_t \to 1$, $E^\cong \to (E^\cong)'$ to weak equivalences.*

*Proof.* We recall that we define $J$ as the reunion of the set of generating acyclic cofibrations of $\operatorname{Seg}(A)$ and of $\{[e, 1]_t \to (E^\cong)'\}$ and $\{E^\cong \to (E^\cong)'\}$ and we suppose that it includes

121