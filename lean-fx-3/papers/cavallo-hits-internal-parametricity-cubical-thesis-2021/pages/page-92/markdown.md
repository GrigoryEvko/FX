80

Cubical type theory

A presheaf $G \in PSh(\widehat{\mathbb{D}}_c)$, then, is a family of sets $G(\Psi)$ indexed by interval contexts (which we think of as the elements in context $\Psi$) with a function $G(\psi) : G(\Psi) \to G(\Psi')$ for every $\Psi' \Vdash \psi \in \Psi$ (which we think of as the action of interval substitution on those elements). Note the analogy to a context $\Gamma$ ctx of one of our cubical type theories: for every $\Psi$, we have the set of closing substitutions $\Psi \Vdash \gamma \in \Gamma$ (modulo equality), and given $\Psi' \Vdash \psi \in \Psi$ and $\Psi \Vdash \gamma \in \Gamma$ we have an induced $\Psi' \Vdash \gamma\psi \in \Gamma$. In accordance with this analogy, cubical sets can serve as an alternative interpretation of the contexts of our cubical formalism, with substitutions between contexts interpreted as morphisms of presheaves.

To interpret the interval judgment, we make use of the Yoneda embedding $\mathfrak{L}$, which takes objects of the indexing category to objects of the presheaf category.$^1$

Definition 3.3.4. Given $c \in \mathcal{C}$, we define $\mathfrak{L}(c) \in PSh(\mathcal{C})$ by $\mathfrak{L}(c)(d) := \mathcal{C}[d, c]$ and $\mathfrak{L}(c)(f) := (-) \circ f$.

We have an interval presheaf $\mathbb{I} := \mathfrak{L}(x:\mathbb{I}) \in PSh(\widehat{\mathbb{D}}_c)$ defined as the Yoneda embedding of the single-interval context. By definition, the elements of $\mathbb{I}(\Psi)$ at a context $\Psi$ are the substitutions $\Psi \Vdash \psi \in (x:\mathbb{I})$, which is to say interval terms $\Psi \Vdash r \in \mathbb{I}$. We then interpret open interval terms $\Gamma \vdash r : \mathbb{I}$ as morphisms $[[r]] \in PSh(\widehat{\mathbb{D}}_c)[[[\Gamma]], \mathbb{I}]$ from the context's interpretation (a cubical set) into this interval presheaf. Context extension by an interval hypothesis is interpreted by (pointwise) product of presheaves: $[[\Gamma.\mathbb{I}]] := [[\Gamma]] \times \mathbb{I}$ where $([[\Gamma]] \times \mathbb{I})(\Psi) := [[\Gamma]](\Psi) \times \mathbb{I}(\Psi)$.

Types over a context $\Gamma$, meanwhile, are interpreted as families indexed by elements of $[[\Gamma]]$ and equipped with interpretations of the Kan operations. First, let us define an intermediate notion of semantic pretype.

Definition 3.3.5. Given a presheaf $G$, a semantic pretype over $G$ is a family $T$ of sets $T(\Psi, g)$ indexed by pairs of $\Psi \in \widehat{\mathbb{D}}_c$ and $g \in G(\Psi)$ and equipped with transition functions $T(\psi, g) : T(\Psi, g) \to T(\Psi', G(\psi)(g))$ for every $\Psi' \Vdash \psi \in \Psi$ such that $T(id_\Psi) = id_{T(\Psi, g)}$ and $T(\psi\psi') = T(\psi') \circ T(\psi)$.

Again, this matches the computational setting, where an open pretype $\Gamma \gg A$ type is defined by the elements of its instances $\Psi \Vdash A\gamma$ type for $\Psi$ ictx and $\Psi \Vdash \gamma \in \Gamma$. Note that given a transformation $\alpha : H \to G$ of syntactic contexts, we can reindex $T$ above to get a semantic pretype $\alpha^*T$ over $H$: $(\alpha^*T)(\Psi, h) := T(\Psi, \alpha(\Psi)(h))$ and $(\alpha^*T)(\psi, h) := T(\psi, \alpha(\Psi)(h))$. We thereby interpret substitution on types.

Syntactic elements are interpreted by families of semantic elements.

$^1$We employ the character $\mathfrak{L}$ ("yo") from the Japanese hiragana syllabary to represent the Yoneda embedding. The stylized $\mathfrak{L}$ symbol used here was created by Favonia.