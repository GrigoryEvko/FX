3.1. PRELIMINARIES

We then define the degree functor $ob(\Delta[B]) \to \mathbb{N}$ by the formula $d([b, n]) = d(b)d(n)$. The subcategory $(\Delta[B])_+$ is the image of $\Delta_+ \times B_+$, and the subcategory $(\Delta[B])_-$ is the image of $\Delta_- \times B_-$.

We recall that we suppose that the Reedy category $B$ is elegant. Let $X$ be a presheaf on $\Delta[B]$, $[a, n]$ an element of $\Delta[A]$, $[f, g] : [a, n] \to [a', n']$ and $[h, i] : [a, n] \to [a', n']$ two negative morphisms, an element $x$ of $X([a, n])$, two non degenerate elements $y \in X([a', n'])$ and $z \in X([a'', n''])$ such that $[f, g]^*y = x$, $[h, i]^*z = x$.

We suppose first that $n \neq 0$. We denote $\pi : B \times \Delta \to \Delta[B]$ the canonical projection and

$$\pi^* : \mathrm{Psh}(\Delta[B]) \to \mathrm{Psh}(\Delta \times B)$$

the functor obtained by precomposing. Remark that for any $a, n$, $(\pi^*X)(a, n) = X([a, n])$. Furthermore, we have again equalities $(f, g)^*y = x$, $(h, i)^*z = x$. As $\Delta \times B$ is Reedy elegant, this implies that $f = h$, $g = i$ and $y = z$.

If $n = 0$, then $[f, g]$ and $[h, i]$ are the identity, and we directly have $y = z$. The Reedy category $\Delta[B]$ is then elegant.

**Definition 3.1.1.5.** We define the simplicial set $E^{\cong}$ as the colimit of the diagram:

$$[e, 0] \leftarrow [e, 1] \xrightarrow{[e, d^1 d^3]} [e, 3] \xleftarrow{[e, d^0 d^2]} [e, 1] \to [e, 0].$$

An *elementary anodyne extension* is one of the following:

(1) The *generating Reedy cofibrations*:

$$[a, n] \cup [b, \partial[n]] \to [b, n], \text{ for } a \to b \text{ a generating acyclic cofibration of A.}$$

(2) The *Segal extensions*:

$$[a, 1] \cup [a, 1] \cup \ldots \cup [a, 1] \to [a, n], \text{ for } a \text{ an object of } A \text{ and } n > 0.$$

(3) The *completeness extensions*:

$$\{0\} \to E^{\cong}.$$

**3.1.1.6.** A *Segal A-category* is a Segal $A$-precategory having the right lifting property against all elementary anodyne extensions.

Let $C$ be a Segal $A$-categories. We define the presheaf $ho(C) : \Delta^{op} \to \mathbf{Set}$ sending $[n]$ to $\mathrm{Hom}_{ho(A)}(e, C_n)$. As explained in [Sim11, § 14.5], this simplicial set has the unique right lifting property against Segal's maps, and is then the nerve of a category that we also note by $ho(C)$. An arrow $x : [e, 1] \to C$ is an *isomorphism* if its image in $ho(C)$ is.

117