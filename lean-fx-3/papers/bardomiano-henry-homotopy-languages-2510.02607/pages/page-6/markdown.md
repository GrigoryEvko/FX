in section C.1 and in section 2.4 we explain in detail how this language of $\mathcal{M}$ actually talks about the objects of $\mathcal{M}$ and prove the first two invariance theorems mentioned above.

To give a general picture of how this language works, if $\mathcal{M}$ is our model category, each formula in the language has a “context” $C$, which informally can be thought of as the list of free variables that can appear in the formula as well as their types. This “context” $C$ is concretely just a cofibrant object of $\mathcal{M}$. An interpretation of the context $C$ into an object $X \in \mathcal{M}$ is just a map $v : C \rightarrow X$. And given $\phi$ a formula in context $C$ and $v : C \rightarrow X$ a map, $\phi(v)$ can be either true or false. We write

$$M \vdash \phi(v)$$

if $\phi(v)$ is true.

Section 2 ends with our first two invariance theorems, stated as theorem 2.38:

**$1^{st}$ Invariance Theorem.** *If $X$ is fibrant and $v : C \rightarrow X$ is homotopic to $v' : C \rightarrow X$ then $M \vdash \phi(v) \Leftrightarrow M \vdash \phi(v')$.*

**$2^{nd}$ Invariance Theorem.** *If $F : X \rightarrow Y$ is a weak equivalence between fibrant objects, then $X \vdash \phi(v) \Leftrightarrow Y \vdash \phi(f(v))$.*

To give a more concrete example of all this, when $\mathcal{M}$ is the canonical or folk model structure on categories, our construction recovers the language of categories as in [Fre76] or [Bla78]. Now, the formula

$$\forall Z \in \text{Ob}, \forall g, h \in \text{Hom}(Y, Z), g \circ f = h \circ f \Rightarrow g = h$$

is a formula in context $X, Y \in \text{Ob}, f \in \text{Hom}(X, Y)$ which corresponds to the (cofibrant) category $\mathcal{C}$ which has two objects $X$ and $Y$ and a unique non-identity arrow $f : X \rightarrow Y$. A map from $\mathcal{C}$ to another category $\mathcal{D}$ is the choice of an arrow $f$ in $\mathcal{D}$ and $\phi(f)$ is true if and only if $f$ is an epimorphism. The second invariance theorem says (in this special case) that equivalence of categories preserves epimorphisms, and the first invariance theorem that if $f$ is isomorphic to another arrow then one is an epimorphism if and only if the other is.

In section 3 we show how our notion of language specializes to many classical model structures. We also discuss briefly some general (but informal) tools to construct this language explicitly for any model structure.

6