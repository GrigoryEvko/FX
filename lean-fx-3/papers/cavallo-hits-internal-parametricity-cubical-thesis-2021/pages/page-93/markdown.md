Formalism and models 81

**Definition 3.3.6.** Given a presheaf $G$ and pretype $T$ over $G$, a *semantic term* in $T$ is a family of elements $t(\Psi, g) \in T(\Psi, g)$ indexed by $\Psi \in \widehat{\mathbb{D}}_c$ and $g \in G(\Psi)$ such that $T(\psi)(t(\Psi, g)) = t(\Psi', G(\psi)(g))$.

Finally, a semantic type is a pretype equipped with operations interpreting the rules for coercion and homogeneous composition.

**Definition 3.3.7.** Given a presheaf $G$ and semantic pretype $T$ over $G$, a *coercion operator* $c$ for $T$ is a family of elements as follows: for every $\Psi \in \widehat{\mathbb{D}}_c$, interval terms $r, s \in \mathbb{I}(\Psi)$, context element $g \in G(\Psi, x : \mathbb{I})$, and $t \in T(\Psi, G(\mathrm{id}_{\Psi}, r/x)(g))$, we require an element $c(\Psi, r, s, g, t) \in T(\Psi, G(\mathrm{id}_{\Psi}, s/x)(g))$. We ask that these satisfy the following properties.

- $T(\psi)(c(\Psi, r, s, g, t)) = c(\Psi', r\psi, s\psi, G(\psi)(g), T(\psi, g)(t))$ for every $\Psi' \Vdash \psi \in \Psi$.
- $c(\Psi, r, r, g, t) = t$.

We similarly define the concept of homogeneous composition operator for a semantic pretype. A *semantic type* is then a triple $(T, c, h)$ consisting of a semantic pretype with accompanying coercion and homogeneous composition operators.

For interpretations of the individual type formers, we refer to [ABCFHL19], which describes a family of models for a cartesian cubical type theory (broadly similar to ours) in settings such as $PSh(\widehat{\mathbb{D}}_c)$. One may also turn to [BCH13; CCHM15; OP18; LOPS18; CMS20] for presheaf-based or presheaf-like models of other variations of cubical type theory.