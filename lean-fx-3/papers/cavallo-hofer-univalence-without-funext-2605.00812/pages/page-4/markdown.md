CAVALLO, HÖFER

**Remark 2.4** The isomorphisms in the wild category $\mathcal{U}$ are exactly the categorical equivalences introduced in Section 1. To avoid confusion, we refer to a pair of functions $s: A \to B$ and $r: B \to A$ between types such that $rs \sim \mathrm{id}_A$ as a *homotopy section* and *homotopy retraction* respectively. The term *isomorphism* is sometimes used in the literature to refer to what the HoTT Book [44] calls *quasi-inverses*, that is, maps $f: A \to B$ and $g: B \to A$ with homotopies $gf \sim \mathrm{id}_A$ and $fg \sim \mathrm{id}_B$. We never use the term in this way.

The following holds by a Yoneda style argument.

**Lemma 2.5** *For a morphism $f: x \to y$ in a wild category $\mathbb{C}$, the following are logically equivalent:*

(i) $f$ is an isomorphism,
(ii) $f^*: \mathbb{C}(x, z) \to \mathbb{C}(y, z)$ is an equivalence for all $z: \mathbb{C}$,
(iii) $f_*: \mathbb{C}(z, y) \to \mathbb{C}(z, x)$ is an equivalence for all $z: \mathbb{C}$.

**Lemma 2.6** *Given an isomorphism $f: x \to y$ in a wild category, the type $\operatorname{Sec}(f)$ is contractible.*

**Proof.** Denote by $f^{-1}$ the retraction of $f$. By Lemma 2.5 and [36, Exercise 9.1] we have the equivalences $(\sum_{g:y \to x} fg = \mathrm{id}_y) \simeq (\sum_{g:y \to x} f^{-1}(fg) = f^{-1}\mathrm{id}) \simeq (\sum_{g:y \to x} g = f^{-1})$. In the last step we use that composition with a path is an equivalence. The last type is contractible. □

**Corollary 2.7** *For a morphism $f$ in a wild category, $\operatorname{is-iso}(f)$ is a proposition.*

**Proof.** We show that $\operatorname{is-iso}(f)$ is contractible, assuming that $f$ is an isomorphism [36, Proposition 12.1.3]. By Lemma 2.6 and its dual, both $\operatorname{Sec}(f)$ and $\operatorname{Ret}(f)$ are contractible. □

**Lemma 2.8** *Isomorphisms in a wild category satisfy 2-out-of-3.*

**Proof.** By associativity we have $(fg)^* \sim f^*g^*$. The structure of an equivalence transfers across homotopies. Hence, the claim follows from 2-out-of-3 for equivalences [36, Exercise 9.4]. □

For every object $x: \mathbb{C}$ in a wild category, the identity $\mathrm{id}_x: x \to x$ is an isomorphism. By path induction, we may generalize to a map $\operatorname{id-to-iso}: x =_{\mathbb{C}} y \to x \cong_{\mathbb{C}} y$ for $x, y: \mathbb{C}$. We define [11, Definition 4.16]:

**Definition 2.9** A wild category $\mathbb{C}$ is *univalent* if $\operatorname{id-to-iso}: x =_{\mathbb{C}} y \to x \cong_{\mathbb{C}} y$ is an equivalence for $x, y: \mathbb{C}$.

**Lemma 2.10** *A wild category $\mathbb{C}$ is univalent exactly if $\sum_{y:\mathbb{C}} x \cong_{\mathbb{C}} y$ is contractible for all $x$.*

**Proof.** By the fundamental theorem of identity types [36, Theorem 11.2.2]. □

Univalence of a universe $\mathcal{U}$ ($\mathrm{UA}_{\mathcal{U}}$, Definition 1.2) cannot be formulated on the level of an arbitrary wild category, as it refers to homotopy of functions. As $\mathrm{UA}_{\mathcal{U}}$ implies $\mathsf{FE}_{\mathcal{U}}$, however, it also implies that $\mathcal{U}$ is a univalent wild category. Absent $\mathsf{FE}_{\mathcal{U}}$, the converse may fail: as we will see, $\mathcal{U}$ can be a univalent wild category without $\operatorname{id-to-eq}$ being an equivalence. We can consider ordinary univalence as the conjunction of two equivalences: one between $A =_{\mathcal{U}} B$ and $A \cong_{\mathcal{U}} B$ and one between $A \cong_{\mathcal{U}} B$ and $A \simeq B$.

### 2.2 Categorical equivalences and function extensionality

In comparing $A \cong_{\mathcal{U}} B$ and $A \simeq B$, it is natural to forget about universes entirely. Recall from Section 1 that a function $f: A \to B$ between (possibly large) types is a *categorical equivalence* if it admits a section and retraction, that is, $s, r: B \to A$ with $fs = \operatorname{id}$ and $rf = \operatorname{id}$. We write $\operatorname{is-ceq}(f)$ for the type of witnesses that $f$ is a categorical equivalence, and $A \cong B$ for the type of categorical equivalences from $A$ to $B$.

In $\operatorname{ITT}$, the only closed categorical equivalences are the strict isomorphisms, such as $A \times B \cong B \times A$. With $\mathrm{CUA}_{\mathcal{U}}$ (Definition 1.3), there are more; for example, any $e: A \cong B$ in $\mathcal{U}$ yields $(a =_A a') \cong (ea =_B ea')$ for $a, a': A$. The map $\operatorname{ceq-to-eq}: (A \cong B) \to (A \simeq B)$, which converts equalities in function types to homotopies, becomes an equivalence under $\mathsf{FE}$. In fact, it is an equivalence *only* if $\mathsf{FE}$ holds.

**Definition 2.11** *Equivalence improvement ($\mathsf{EI}$) is the principle that for all types $A, B$, the map $\operatorname{ceq-to-eq}: (A \cong B) \to (A \simeq B)$ is an equivalence.*

We recall a lemma familiar from proofs that $\mathrm{UA}_{\mathcal{U}}$ implies $\mathsf{FE}_{\mathcal{U}}$ [44, Theorem 4.9.4] [36, Theorem 17.3.2]:

4