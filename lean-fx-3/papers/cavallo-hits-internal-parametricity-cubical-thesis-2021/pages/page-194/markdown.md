182

Parametric cubical type theory

The characterization of bridges in the universe follows the same blueprint. This time, however, the aim is to identify bridges with relations. In one direction, the bridge type former provides our map from bridges to relations.

$$p : \text{Bridge}(\mathsf{U}, A, B) \quad \mapsto \quad \lambda\langle a, b \rangle . \text{Bridge}(\boldsymbol{x} . p \boldsymbol{x}, a, b) \in A \times B \to \mathsf{U}$$

That is, the relation induced by $p : \text{Path}(\mathsf{U}, A, B)$ relates $a$ with $b$ when there is a bridge from $a$ to $b$ over $p$. We dub the equivalent of univalence relativity.

**Definition 9.4.1 (Relativity).** We say a universe $\mathsf{U}$ closed under bridge types is relativistic if the canonical map $\text{Bridge}(\mathsf{U}, A, B) \to (A \times B \to \mathsf{U})$ defined above is an isomorphism.

To make our universes relativistic, we again introduce a new type former, the Gel type, which converts relations to bridges between types. The operational semantics for Gel types is shown in Figure 9.1. We call them "Gel" types because they share a basic structure with the G operation of the BCH cubical set model [BCH19, §3] but apply to relations rather than isomorphisms.

In comparison to the V type, the Gel type is refreshingly simple: given a relation $\Psi \setminus \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R$ type, it directly produces a bridge between $A_0$ and $A_1$, which is to say a type dependent on a fresh bridge variable $\boldsymbol{r}$. The proofs of the formation, introduction, and elimination rules for Gel are similar in complexity to those we gave for V types in Section 3.1.6.2: there are non-trivial coherence obligations to check, but they are of a fairly simple character.

**Rules 9.4.2 (Gel pretype formation).**

$$\frac{\Psi \Vdash \boldsymbol{r} \in \mathbf{I} \quad (\forall \varepsilon) \Psi \setminus \boldsymbol{r} \Vdash A_\varepsilon = A'_\varepsilon \text{ type} \quad \Psi \setminus \boldsymbol{r}, a_0 : A_0, a_1 : A_1 \gg R = R' \text{ type}}{\Psi \Vdash \text{Gel}_\boldsymbol{r}(A_0, A_1, a_0 . a_1 . R) = \text{Gel}_\boldsymbol{r}(A'_0, A'_1, a_0 . a_1 . R') \text{ pretype}}$$

$$\frac{\varepsilon \in \{0, 1\} \quad \Psi \Vdash A_\varepsilon \text{ type}}{\Psi \Vdash \text{Gel}_\varepsilon(A_0, A_1, a_0 . a_1 . R) = A_\varepsilon \text{ pretype}}$$

Proof. Straightforward by coherent value introduction and expansion respectively.

Note that the term-level arguments of Gel (the types $A_0, A_1$ and the relation $R$) are all precluded from using the interval term $\boldsymbol{r}$. The introduction form for Gel types takes a similar form: an element of $\text{Gel}_\boldsymbol{r}(A_0, A_1, a_0 . a_1 . R)$ consists of a pair of terms and a proof they are related, and draws a bridge across the Gel type between those terms. This is one direction of an isomorphism $\text{Bridge}(\boldsymbol{x} . \text{Gel}_\boldsymbol{x}(A_0, A_1, a_0 . a_1 . R), M_0, M_1) \simeq R[M_0/a_0, M_1/a_1]$ we intend to set up.