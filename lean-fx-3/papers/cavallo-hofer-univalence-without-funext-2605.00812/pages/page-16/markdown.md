CAVALLO, HÖFER

it is defined by substituting the image of the pseudomorphism along the unit. Since $\bigcirc_S f \circ \eta_A \doteq \eta_B \circ f$ the claim follows by Proposition 6.3 and 2-out-of-3 for categorical equivalences (Lemma 2.8).

We show that the type family $I: \mathcal{U}, A, B: \mathsf{Fam}(I) \vdash \mathsf{Iso}(I, A, B) := (A \cong_{\mathcal{U}} B)$ from Section 4.2 is $\bigcirc_S$-modal, which we can use to improve the equivalence in the definition of $\mathsf{CUA}_{\mathcal{U}}^\bullet$ to a categorical equivalence over well-behaved base models.

**Lemma 6.8** If $\mathbb{C} \models \mathsf{CUA}_{\mathcal{U}}^\bullet$, then $\mathsf{Iso}$ in $\mathsf{Poly}(\mathbb{C})$ is $\bigcirc_S$-modal.

**Proof.** By Proposition 6.3, it suffices to show that the positions of $\mathsf{Iso} \in \mathrm{Ty}(1.\mathcal{U}.\mathsf{Fam} \times \mathsf{Fam}, \mathsf{Iso})$ are empty. We work internally to $\mathbb{C}$. We show for all $I: \mathcal{U}_S$, $A \doteq (A_S, A_P)$, $B \doteq (B_S, B_P): \mathsf{Fam}_S(I)$, $e: \mathsf{Iso}_S(I, A, B)$ that $\mathsf{Iso}_P(I, A, B, e) \to 0$, which suffices by strict initiality of 0. By Lemma 4.15, we can assume $A \doteq B$ and $e \doteq \mathrm{id}$. In this case, the functions on positions are given by $\mathsf{in}_1$ and therefore the type (3) is empty. $\square$

**Proposition 6.9** If $\mathbb{C}$ is a model of $\mathsf{ITT} + \mathsf{FE} + \mathsf{UA}_{\mathcal{U}}$ with extensive finite coproducts of types, then $\mathsf{Poly}(\mathbb{C}) \models \mathsf{CCUA}_{\mathcal{U}}$.

**Proof.** By Theorem 4.17, we have $\mathsf{Poly}(\mathbb{C}) \models \mathsf{CUA}_{\mathcal{U}}$. Since the types declared equivalent in the statement of $\mathsf{CUA}_{\mathcal{U}}$ are $\bigcirc_S$-modal, by Lemma 6.8 and the definition of identity types (Proposition 3.8), the claim follows from Lemma 6.7.

**Corollary 6.10** $\mathsf{ITT} + \mathsf{CCUA}_{\mathcal{U}} \not\vdash \mathsf{FE}_{\mathcal{U}}$.

**Proof.** Proposition 5.4 provides a model $\mathbb{C}$ of of $\mathsf{ITT} + \mathsf{FE} + \mathsf{UA}_{\mathcal{U}}$ with extensive finite coproducts of types. We have $\mathsf{Poly}(\mathbb{C}) \models \mathsf{CCUA}_{\mathcal{U}}$ by Proposition 6.9 and $\mathsf{Poly}(\mathbb{C}) \models \neg \mathsf{FE}_{\mathcal{U}}$ by Proposition 5.3.

Finally, we show that while $\mathsf{CCUA}_{\mathcal{U}}$ is still strictly weaker than $\mathsf{UA}_{\mathcal{U}}$, it is strictly stronger than $\mathsf{CUA}_{\mathcal{U}}$.

**Proposition 6.11** $\mathsf{ITT} + \mathsf{CUA}_{\mathcal{U}}^\bullet \not\vdash \mathsf{CCUA}_{\mathcal{U}}$.

**Proof.** Take $\mathbb{C}$ to be a model of $\mathsf{ITT} + \mathsf{FE} + \mathsf{UA}_{\mathcal{U}}$ with extensive finite coproducts of types, as provided by Proposition 5.4. Then $\mathsf{Poly}(\mathbb{C}) \models \mathsf{CUA}_{\mathcal{U}}^\bullet$ by Theorem 4.17. As in the proof of Theorem 6.1, we now consider the slice model $\mathsf{Poly}(\mathbb{C}) / \top\langle 1 \rangle$ for $\top\langle - \rangle$ from Definition 5.1. This time, however, we modify the interpretation of the identity type.

We define our new identity types by $(u ='_A v) := (u =_A v) \times \top\langle 1 \rangle$, where $u =_A v$ is the identity type in $\mathsf{Poly}(\mathbb{C})$. Since $\top\langle 1 \rangle$ is a proposition by Lemma 4.16, it is contractible in the slice, so the projection $(u ='_A v) \to (u =_A v)$ is an equivalence and in particular $u ='_A v$ is an identity type. If we write $\cong'$ for wild-categorical isomorphisms defined with $='$, it follows also that $(a \cong_{\mathbb{D}} b) \simeq (a \cong'_{\mathbb{D}} b)$ for any wild category $\mathbb{D}$. Thus $\mathsf{CUA}_{\mathcal{U}}^\bullet$, which holds in $\mathsf{Poly}(\mathbb{C})$ by Theorem 4.17, transfers to the slice model with the new identity type.

However, $\mathsf{CCUA}_{\mathcal{U}}$ cannot hold (in or out of the slice) when formulated with $='$ and $\cong'$. For $A, B: \mathcal{U}$, the family of positions for $(A ='_\mathcal{U} B)$ is the constant family 1. The family of positions for $A \cong'_\mathcal{U} B$, which is categorically equivalent to $(A \cong_\mathcal{U} B) \times \top\langle 1 \rangle \times \top\langle 1 \rangle$, is the constant family $1+1$ (using Lemma 6.8). Thus, by Lemma 4.14, the equivalence $(A ='_\mathcal{U} B) \simeq (A \cong' B)$ is only categorical when both sides are empty.

### 6.3 Approximate univalence

Van den Berg [46, Definition 2.13] defines another weak form of $\mathsf{UA}_{\mathcal{U}}$, in the language of path categories, which can be rendered in type theory as follows.

**Definition 6.12** *Approximate univalence* ($\mathsf{UA}_{\mathcal{U}}^\sim$) is the principle that for all $A, B: \mathcal{U}$ and $e: A \simeq B$, we have some $p: A =_\mathcal{U} B$ such that $\mathsf{id\text{-}to\text{-}eq}(p) \sim e$.

Notably, $\mathsf{UA}_{\mathcal{U}}^\sim$ can be expressed as an inference rule without $\Pi$ types. In the presence of $\Pi$ types, Swan [43, Remark 4.6] comments that it is an open question whether $\mathsf{UA}_{\mathcal{U}}^\sim$ implies $\mathsf{FE}_{\mathcal{U}}$. An immediate but subtle consequence of $\mathsf{UA}_{\mathcal{U}}^\sim$ is that there is a composite map $(A \simeq B) \to (A =_\mathcal{U} B) \to (A \cong B)$ that improves any homotopy equivalence to a homotopic categorical equivalence. In light of the decomposition of $\mathsf{UA}_{\mathcal{U}}$ in Section 2.2, it is natural to consider an analogue of Definition 2.11:

16