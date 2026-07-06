Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:47

6.1. Judgments and cubical type theory. We recall the presheaf interpretation of the judgments of cubical type theory developed in [CCHM15, ABC$^{+}$19], which draw on earlier presheaf interpretations of dependent type theory [Hof97].

Definition 6.4. A semantic context is a presheaf $G \in [\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$; a semantic substitution between contexts $G', G$ is a presheaf morphism (i.e., natural transformation) $\alpha : G' \to G$.

Definition 6.5. A semantic pretype over a context $G \in [\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ is a presheaf $T \in [(\int G)^{\mathrm{op}}, \mathbf{Set}]$ over the category of elements $\int G$, which is to say the following data:

$\triangleright$ for every $\Psi \in \square_{ca}$ and $g \in G(\Psi)$, a set $T(\Psi, g)$;

$\triangleright$ for every $\Psi' \Vdash \psi \in \Psi$ and $g \in G(\Psi)$, a map $T(\psi) : T(\Psi', G(\psi)(g)) \to T(\Psi, g)$.

Definition 6.6. A semantic element $t$ of a pretype $T$ in context $G$ is a family of elements $t(\Psi, g) \in T(\Psi, g)$ indexed by $\Psi \in \square_{ca}$ and $g \in G(\Psi)$ such that $T(\psi)(t(\Psi, g)) = t(\Psi', G(\psi)(g))$ for every $\Psi' \Vdash \psi \in \Psi$ and $g \in G(\Psi)$.

A semantic type is then a pretype equipped with coercion and homogeneous composition operators implementing the rules shown in Figure 2. We give the definition of coercion operator here and leave it to the reader to infer the corresponding notion of homogeneous composition operator.

Definition 6.7. Given a pretype $T$ over $G$, a coercion operator $c$ for $T$ is a family of elements as follows: for every $\Psi \in \square_{ca}$, interval terms $\Psi \Vdash r, s \in \mathbb{I}$, element $g \in G(\Psi, x : \mathbb{I})$, and $t \in T(\Psi, G(\mathsf{id}_{\Psi}, r/x)(g))$, we require an element $c(\Psi, r, s, g, t) \in T(\Psi, G(\mathsf{id}_{\Psi}, s/x)(g))$. We ask that these satisfy the following properties.

$\triangleright$ $T(\psi)(c(\Psi, r, s, g, t)) = c(\Psi', r\psi, s\psi, G(\psi)(g), T(\psi)(t))$ for every $\Psi' \Vdash \psi \in \Psi$.

$\triangleright$ $c(\Psi, r, r, g, t) = t$.

Definition 6.8. A semantic type $(T, c, h)$ over $G$ is a triple consisting of a semantic pretype $T$ over $G$ with coercion and homogeneous composition operators $c$ and $h$.

Remark 6.9. A semantic substitution $\alpha : G' \to G$ acts on types and terms over $G$ by reindexing; we write $\alpha^*T$ and $\alpha^*t$ for the action on types and terms respectively.

Definition 6.10. A semantic interval term over $G$ is a presheaf morphism $r : G \to \mathcal{K}(x : \mathbb{I})$. A semantic constraint is a morphism $r : G \to \Omega_{dec}$ where $\Omega_{dec}$ is the decidable subobject classifier in $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$, which classifies monomorphisms $m : H' \mapsto H$ in $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ such that $m(\Psi)$ has decidable image for all $\Psi$.

Angiuli et al.'s [ABC$^{+}$19, Theorem 1] shows that cartesian cubical type theory can be interpreted using these semantic judgments in any presheaf category whose base category contains a suitably structured interval object.

Proposition 6.11. $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ interprets cubical type theory with an infinite hierarchy of univalent universes, each closed under dependent function and product types, Path-types, and V-types.

Proof. By Angiuli et al.'s Theorem 1 [ABC$^{+}$19]. The formulation of cartesian cubical type theory given there is slightly different from our own (for example taking com rather than coe and hcom as primitive), but not in any essential way.

We note that the statement of the theorem in [ABC$^{+}$19] requires that the base category is closed under finite products, which is not the case for $\square_{ca}$: the cartesian product of the contexts $(\boldsymbol{x} : \mathbf{I})$ and $(\boldsymbol{y} : \mathbf{I})$ does not exist. However, the proof only actually requires that the product functor $- \times (x : \mathbb{I})$ exists, and this is indeed the case in $\square_{ca}$.