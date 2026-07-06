Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz

## 4 The universe of amazingly cocartesian types

We now turn to the construction of Cat. As mentioned in the introduction, Cat will be a subtype of $\mathcal{U}$ and therefore must be classified by a proposition $\mathcal{U} \to \text{HProp}$. The most obvious choice of proposition is something akin to being cocartesian, but a moment's thought reveals this is unworkable: if we are to define a map isCocartFib : $\mathcal{U} \to \text{HProp}$, what should the input be cocartesian over? Cocartesianness is a property of families!

To fix this, we follow Licata et al. [18] as refined in the context of directed type theories [10, 42]. First, consider a general notion of fibration isFib$_X$: $\mathcal{U}^X \to \text{HProp}$. The goal is to define a predicate that witnesses fibrancy of a type $A$ viewed as a family over the entire ambient context. From isFib$_\mathbb{I}$ : $\mathcal{U}^\mathbb{I} \to \text{HProp}$, Lemma 2.9 yields precisely such a notion of fibrancy. Moreover, this stronger notion of fibration can be shown to agree with the classical notion when we restrict attention to b-annotated families.

We will now apply this construction, leveraging Theorem 3.8.

Lemma 4.1. If $A: X \to \mathcal{U}_\square$ is iso-inner, then hasLCCLifts($A$) and LCCLiftsCompose($A$) are propositions.

Let us write $i: \Delta^2 \to \mathbb{I}^2$ for the canonical inclusion. Using Lemma 2.9, we now transpose isInner($-\circ i$), hasLCCLifts, and LCCLiftsCompose($-\circ i$) to obtain elements of $\mathcal{U} \to \mathcal{U}$, namely aisInner, aHasLCCLifts, and aLCCLiftsCompose. Here we have used $i$ as, e.g., isInner takes $\Delta^2 \to \mathcal{U}$ not $\mathbb{I}^2 \to \mathcal{U}$.

We then define Cat:

$$\text{Cat} := \sum_{A: \mathcal{U}_\square} \begin{array}{l} \text{isRezk } A \times \text{aisInner } A \\ \times \text{aHasLCCLifts } A \times \text{aLCCLiftsCompose } A \end{array}$$

Lemma 4.2. Cat is a subtype of $\mathcal{U}_\square$.

Theorem 4.3. Cat is the base of the universal cocartesian family, i.e., for any $C$ : $\mathcal{U}$, we have $\langle b \mid C \to \text{Cat} \rangle \simeq \langle b \mid \sum_{E:C \to \mathcal{U}} \text{isCocart}(E) \rangle$.

PROOF. Fix $A$ : $X \to \mathcal{U}_\square$. Our goal is to show that $A$ factors through Cat if and only if $A$ is cocartesian. To prove this, let us consider the data involved in a factorization through Cat. By definition, this is equivalent to factoring through four distinct subobjects of $\mathcal{U}_\square$: those carved out by isRezk, aisInner, aHasLCCLifts, and aLCCLiftsCompose. In the latter three cases, we may analyze these subobjects using the transpositions used to define them.

For instance, if $A$ factors through $\sum_{B: \mathcal{U}_\square}$ aisInner($B$), then there is an element of the following type by Lemma 2.9:

$$\langle b \mid \prod_{x:X \bowtie} \text{isInner}(A \circ x \circ i) \rangle$$

Such an element exists if and only if $A$ is an inner fibration.

This reasoning applies to aHasLCCLifts and aLCCLiftsCompose so we may conclude that $A$ factors through Cat if and only if it is iso-inner, locally cocartesian, and locally cocartesian edges compose. The desired bi-implication is then Theorem 3.8. $\square$

## 5 The category of categories

In this section, we leverage Theorem 4.3 to prove the crucial properties of Cat. Namely, we prove Cat is Segal and Rezk, satisfies directed univalence as described in Section 1, and is simplicial. Combining these results together we show that Cat is a category and, in particular, the category of categories.

## 5.1 Classifying cocartesian fibrations

The main input to the proofs that Cat is Segal and Rezk is a characterization of cocartesian fibrations over $\Delta^n \times C$ where $C$ is a category. To see why, note that by Theorem 4.3, we know that $f$ : $X \times \Delta^n \to \text{Cat}$ is determined by a cocartesian family over $X \times \Delta^n$. By giving a precise description of such families, we obtain a more tractable version of, e.g., the restriction map $\langle b \mid \mathbb{I}^n \times \Delta^2 \to \text{Cat} \rangle \to \langle b \mid \mathbb{I}^n \times \Delta^2_1 \to \text{Cat} \rangle$. This version will be manifestly invertible, and so we can conclude that Cat is Segal. A key lemma in this process is the following:

Lemma 5.1. For $X$ : $\mathcal{U}$ a category and $A, B$ : $X \to \mathcal{U}$ cocartesian, a cocartesian functor $\alpha: \prod_{X:X} A(x) \to B(x)$ induces an equivalence of total categories $\widetilde{\alpha}: \widetilde{A} \simeq \widetilde{B}$ iff $\prod_{x:\widetilde{A}} \text{isEquiv}(\alpha(x))$ holds.

PROOF. Since cocartesian families are isofibrations, we know that $\widetilde{A}$ and $\widetilde{B}$ are both categories themselves. By Lemma 2.12, we check that $\widetilde{\alpha}$ is fully faithful, and essentially surjective.

Essential surjectivity is straightforward: given $(x, b)$ : $\widetilde{B}$, we take $(x, \alpha(x)^{-1}(b))$ as $\alpha$ is invertible on $b$ elements of $X$. To show that $\widetilde{\alpha}$ is fully faithful, note that transport induces an equivalence between $\mathbb{I} \to \widetilde{A}$ and $\sum_{x:\mathbb{I}\to X} \sum_{a_0:A(x0),a_1:A(x1)} \text{hom}_{A(x1)}(x_1 a_0, a_1)$. Since $\alpha$ preserves cocartesian edges, it therefore suffices to show that $\text{hom}_{A(x_1)}(x_1 a_0, a_1) = \text{hom}_{B(x_1)}(\alpha(x1, x_1 a_0), \alpha(x1, a_1))$ for $x$ : $\mathbb{I} \to X$ and $a_\epsilon$ : $A(x\epsilon)$. This holds as $\alpha(x1)$ is invertible. $\square$

Next we show that every cocartesian family $A$ : $X \times \mathbb{I} \to \mathcal{U}$, where $X$ is a category, is of the form $\text{Gl}(A(-, 0), A(-, 1), \lambda x. (x, -)_!)$. To this end, we note the following:

Lemma 5.2. Given $A$ as above, the transport map $\alpha = \lambda x. (x, -)_!$ is a cocartesian functor $A(-, 0) \to A(-, 1)$.

PROOF. Unfolding, this follows from the 3-for-2 condition which holds for cocartesian arrows [5, Proposition 5.1.8]. $\square$

Consequently, $B = \text{Gl}(A(-, 0), A(-, 1), \alpha)$ is a cocartesian family. Moreover, we can produce a map of families $A \to B$:

$$\text{glue}(x, i, a) = (x, i, ((x, i \vee -)_! a, \lambda p: i = 0. p_! a))$$

In words, we use cocartesian transport to move $a: A(x, i)$ to $A(x, 1)$ and, if $i = 0$ to begin with, record the original $a$ as well.

Lemma 5.3. glue: $\prod_{p:X \times \mathbb{I}} A(p) \to B(p)$ is a cocartesian functor.

PROOF. Following Buchholtz and Weinberger [5, Theorem 5.3.19], to check that glue is cocartesian, it suffices to check that the Beck-Chevalley natural transformation is invertible. By Lemma 2.11, it suffices to check this on $b$ elements where it is immediate. $\square$

Corollary 5.4. glue is an equivalence of cocartesian families.

PROOF. Applying Lemma 5.1, it suffices to check this equivalence fiberwise on $b$-annotated elements $(x, i)$ : $X \times \mathbb{I}$. In particular, it suffices to check that induces an equivalence on $b$-annotated elements of $\mathbb{I}$ which, by Axiom 4, consists only of 0 and 1. However, over 0 and 1 we see that glue is an equivalence: over 0, this is immediate and over 1 it follows from the observation that cocartesian transport over the identity arrow is the identity. $\square$