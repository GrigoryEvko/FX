arXiv:2307.06664v2 [math.CT] 9 Oct 2024

# When does \(\mathrm{Ind}_{\kappa}(C^I)\simeq \mathrm{Ind}_{\kappa}(C)^I?\)

Simon Henry

## Abstract

We investigate under which condition the  \( \kappa \) -ind completion of a functor category  \( C^{I} \)  is equivalent to the category of functors from I to the  \( \kappa \) -ind completion of C. A published theorem implies this is true for any Cauchy complete category C and  \( \kappa \) -small category I, but we show this is not the case in general. We prove two results that seem to cover all applications of this incorrect theorem we could find in the literature: The result holds if C has  \( \kappa \) -small colimits and I is  \( \kappa \) -small, or if C is an arbitrary category and I is well-founded and  \( \kappa \) -small. In both cases, we show that the conditions are optimal in the sense that the result holds for all C if and only if I satisfies the given assumption.

## Contents

1 Introduction 1
2 Proof of Theorem 1.2. 4

2.1 Proof of (L1) or (L2) \(\Rightarrow\) (L3) 6
2.2 Proof of (L3) \(\Rightarrow\) (L1) 7

3 Proof of Theorem 1.3. 8

3.1 Well-founded categories 8
3.2 Proof of (A2) \(\Rightarrow\) (A4) 11
3.3 Proof of (A4) \(\Rightarrow\) (A1) 12

## 1 Introduction

Given \(\kappa\) a regular cardinal and \(C\) a category we denote by \(\mathrm{Ind}_{\kappa}(\mathcal{C})\) the \(\kappa\)-ind completion of \(\mathcal{C}\), that is the pseudo-initial object in the locally full subcategory of \(\mathcal{C} \backslash \mathbf{Cat}\) whose objects have \(\kappa\)-filtered colimits and morphisms are functors preserving these \(\kappa\)-filtered colimits. \(\mathrm{Ind}_{\kappa}(\mathcal{C})\) can be explicitly described as the full subcategory of the presheaf category \(\mathbf{Sets}^{\mathcal{C}^{\mathrm{op}}}\) of functors that are small \(\kappa\)-directed colimits of representables. If \(\mathcal{C}\) is small this is also equivalent to the category of \(\kappa\)-flat functors \(\mathcal{C}^{\mathrm{op}} \to \mathbf{Sets}\).

The construction \(\mathrm{Ind}_{\kappa}\) is a covariant endofunctor functor of the bicategory of locally small categories. In particular, for each \(i\in I\) the evaluation functor \(ev_{c}:\mathcal{C}^{I}\to \mathcal{C}\), induces a functor preserving \(\kappa\)-filtered colimits \(\mathrm{Ind}_{\kappa}(C^{I})\to \mathrm{Ind}_{\kappa}(C)\), which together induce a functor:

2020 Mathematics Subject Classification. 18A25, 18C35

email: shenry2@uottawa.ca

1

$$E_{\mathcal{C},\kappa}^{I}: \operatorname{Ind}_{\kappa}(C^{I}) \to \operatorname{Ind}_{\kappa}(C)^{I}$$

which also preserves $\kappa$-filtered colimits.

The goal of this paper is to investigate under which condition on $C, \kappa$ and $I$ this functor $E_{\mathcal{C},\kappa}^{I}$ is an equivalence.

This is also closely related to the question of whether, given an accessible category the category $A^{I}$ is accessible, and what the locally $\kappa$-presentable objects of this category are:

**1.1 Proposition.** *Let $A$ be a $\kappa$-accessible category, with $A_{\kappa}$ its full subcategory of $\kappa$-presentable objects, and $I$ any category, then the following condition are equivalent:*

(1) *The functor*

$$E_{A_{\kappa},\kappa}^{I}: \operatorname{Ind}_{\kappa}(A_{\kappa}^{I}) \to \operatorname{Ind}_{\kappa}(A_{\kappa})^{I}$$

*is an equivalence.*

(2) *The category of functors $I \to A$ is $\kappa$-accessible, with its $\kappa$-presentable objects being the functors $I \to A_{\kappa}$.*

*Proof.* This follows immediately from the fact that a category $A$ is $\kappa$-accessible if and only if $A = \operatorname{Ind}_{\kappa}(A_{\kappa})$. $\square$

From now on, if $A$ is a $\kappa$-accessible category, we denote by $A_{\kappa}$ the category of $\kappa$-presentable objects of $A$.

Here it should be noted that a category $A$ is accessible if and only if it is of the form $A \simeq \operatorname{Ind}_{\kappa}(\mathcal{C})$ with $\mathcal{C}$ a small category. Moreover, in this case, the $\kappa$-presentable objects of $A$ are exactly the retracts of objects of $\mathcal{C}$. So, a category is of the form $A_{\kappa}$ for $A$ a $\kappa$-accessible category if and only if it is Cauchy complete. Hence, the question of whether, for any accessible category $A$, the functor category $A^{I}$ is $\kappa$-accessible with its $\kappa$-presentable objects being the functor $I \to A_{\kappa}$, is exactly the same as the question of whether $E_{\mathcal{C},\kappa}^{I}$ is an equivalence for any Cauchy complete category $\mathcal{C}$.

In [10], Makkai claims (As theorem 5.1) that for any $\kappa$-accessible categories $A$ and any $\kappa$-small category $I$ then the category of functors $I \to A$ is $\kappa$-accessible, with its $\kappa$-accessible objects being the functors $I \to A_{\kappa}$. This would imply that $E_{\mathcal{C},\kappa}^{I}$ is an equivalence for all Cauchy complete category $\mathcal{C}$ for all $I$ a $\kappa$-small category. We will show that this is not the case - and hence that Makkai's theorem is incorrect. This result is used in a few places throughout the literature, the author is aware of [13], [7], [3] and [5]. However, in each of these cases, it seems the use of Makkai's theorem can be replaced by one of the two (correct) theorems below:

**1.2 Theorem.** *For a category $I$ the following conditions are equivalent:*

(L1) *For any locally $\kappa$-presentable category $A$, the category $A^{I}$ is locally $\kappa$-presentable and its $\kappa$-presentable objects are the functors $I \to A_{\kappa}$.*

(L2) *For every category $\mathcal{C}$ with all $\kappa$-small colimits, the functor*

$$E_{\mathcal{C},\kappa}^{I}: \operatorname{Ind}_{\kappa}(C^{I}) \to \operatorname{Ind}_{\kappa}(C)^{I}$$

*is an equivalence.*

2

(L3) $I$ is essentially $\kappa$-small (that is equivalent to a $\kappa$-small category).

# **1.3 Theorem.** For a category $I$ the following conditions are equivalent:

(A1) For every category $\mathcal{C}$ the functor

$$E_{\mathcal{C},\kappa}^I : \text{Ind}_\kappa(C^I) \rightarrow \text{Ind}_\kappa(C)^I$$

is an equivalence.

(A2) For every Cauchy complete category $\mathcal{C}$, the functor $E_{\mathcal{C},\kappa}^I$ above is an equivalence.

(A3) For any $\kappa$-accessible category $A$, the category $A^I$ is $\kappa$-accessible and its $\kappa$-presentable objects are the functor $I \rightarrow A_\kappa$.

(A4) $I$ is essentially $\kappa$-small and well-founded in the sense of Proposition 3.4.

We refer the reader to Proposition 3.3 and Proposition 3.4 for various equivalent definitions of well-founded categories, but one of these characterizations is that $I$ has no non-trivial endomorphisms and that its posetal reflection is a well-founded poset. In particular, in the case of $\kappa = \omega$, condition (A4) means that $I$ is equivalent to a finite category with no non-identity endomorphisms. That fact that $\text{Ind}(C^I) = \text{Ind}(C)^I$ for such category was already proved as Proposition 8.8.5 of exposé I of [4], as well as in C.Meyer PhD Thesis (page 55) [11]. So in this case, our contribution is only to show that this condition is necessary.

Similarly, Proposition 5.3.5.15 from [9] shows in the framework of $\infty$-categories that $E_{\mathcal{C},\kappa}^I$ is an equivalence for any regular cardinal $\kappa$ and any $\infty$-category $\mathcal{C}$ when $I$ is a finite poset. This result can be applied as is to 1-categories, so it does recover a special case of our Theorem 1.3, this time beyond the case $\omega = \kappa$, but with less general conditions on the category $I$.

For an explicit counter-example to Makkai's theorem, the reader should go to Section 3.2, where we show, using an explicit construction, that point (A2), or equivalently (A3), implies point (A4) in Theorem 1.3. In particular, for any $\kappa$-small category $I$ which is *not* well-founded, we will build a category $C = I^{(\kappa)}$ (see Construction 3.1) so that the accessible category $A = \text{Ind}_\kappa(C)$, is such that not every functor in $A^I$ is a $\kappa$-filtered colimit of functors $I \rightarrow A_\kappa$ (here $C = A_\kappa$ because $C = I^{(\kappa)}$ will be Cauchy-complete).

It should be noted that the requirement in conditions (A3) and (L1) that the $\kappa$-presentable objects of $A^I$ are the functors $I \rightarrow A^\kappa$ is absolutely essential to both theorems. For example, in the case of locally presentable categories, we have

# **1.4 Theorem.** Let $\mathcal{C}$ be a locally $\kappa$-presentable category, and $I$ be any small category. Then the category of functors $\mathcal{C}^I$ is locally $\kappa$-presentable.

*Proof.* This follows from Theorem 2.17 of G. Bird PhD thesis [2], which claims that the bicategory of locally $\kappa$-presentable category and $\kappa$-accessible right adjoint functors between them has all **Cat**-enriched pseudo limits and they are preserved by the forgetful functor to **Cat**. The functor category $\mathcal{C}^I$ corresponds to the co-tensor for the locally $\kappa$-presentable category $\mathcal{C}$ by the category $I$. $\square$

3

Hence in Theorem 1.2, condition (L1) could be rephrased as simply: the $\kappa$-presentable objects of $A^I$ are exactly the functor $I \to A_\kappa$.

Finally, after the publication of a first preprint version of the present paper, Leonid Positelski published a result that significantly improved some aspect of our Theorem 1.2 by showing the requirement that the category $A$ is locally presentable can be considerably weakened, without automatically falling under the scope of Theorem 1.3. More precisely, theorem 6.1 of [12] assert that:

**1.5 Theorem** (Positelski [12]). *Let $\kappa$ be a regular cardinal and $\lambda < \kappa$ another infinite cardinal. If $I$ is a $\kappa$-small category and $A$ is a $\kappa$-accessible category which has colimits of $\lambda$-indexed chains, then the category $A^I$ is $\kappa$-accessible and its $\kappa$-presentable objects are the functor $I \to A_\kappa$.*

In particular, using this and Proposition 1.1, we obtain that $\text{Ind}_\kappa(C^I) \simeq \text{Ind}_\kappa(C)^I$ when $I$ is $\kappa$-small and $C$ is Cauchy complete with colimits of $\lambda$-chain for $\lambda < \kappa$ an infinite cardinal.

Note that [12] also proves similar results for more general weighted limits of accessible categories. This result also immediately gives a very good upper bound on the accessibility rank of $A^I$ in general:

**1.6 Corollary** (Positelski). *Let $\kappa$ be a regular cardinal, $I$ a $\kappa$-small category, $A$ a $\kappa$-accessible category and $\lambda$ any regular cardinal such that $\kappa \triangleleft \lambda$. Then $A^I$ is $\lambda$-accessible and its $\lambda$-presentable objects are the functors $I \to A_\lambda$.*

Where $\kappa \triangleleft \lambda$ is the “sharply less” relation from [1, Definition 2.12]. This applies for example of $\lambda = \kappa^+$ is the successor cardinal of $\kappa$.

*Proof.* Under the condition $\kappa \triangleleft \lambda$, the category $A$ is also $\lambda$-accessible and has $\kappa$-directed colimits. In particular it has colimits of chain indexed by $\kappa$ for $\kappa < \lambda$ an infinite cardinal, so we can apply Theorem 1.5 and concludes. $\square$

This paper arose following a discussion on Mathoverflow [6]. In particular, I am especially grateful to Ben Wieland for suggesting a first counter example to the claim that $E_{\omega,\mathcal{C}}^I$ is an equivalence when $I$ is $\omega$-small, which was the starting point to the proof in subsection 3.2, and to Ivan Di Liberti for pointing me to Makkai’s theorem 5.1 in [10].

## 2 Proof of Theorem 1.2.

The equivalence of conditions (L1) and (L2) of Theorem 1.2 follows immediately from Proposition 1.1 and the fact that a $\kappa$-accessible category is locally presentable if and only if its $\kappa$-presentable objects have $\kappa$-small colimits. So we only need to show the equivalence with condition (L3).

We start by observing the following equivalences:

**2.1 Proposition.** *Let $I$ be a category. The following conditions are equivalents:*

(1) *The functor*

$$\text{Hom}(\_\_\_\_\_) : I^{\text{op}} \times I \to \mathbf{Sets}$$

*is a $\kappa$-presentable object of $\mathbf{Sets}^{I^{\text{op}} \times I}$.*

4

(2) $I$-indexed ends, seen as functors:

$$\int_I : \mathbf{Sets}^{I^{\mathrm{op}} \times I} \to \mathbf{Sets}$$

preserves $\kappa$-filtered colimits.

(3) For any category $A$ with $\kappa$-filtered colimits, a functor $I \to A_\kappa$ is $\kappa$-presentable when seen as an object of $A^I$.
(4) For any locally $\kappa$-presentable category $A$, a functor $I \to A_\kappa$ is $\kappa$-presentable when seen as an object of $A^I$.

Moreover, all these condition holds when $I$ is an essentially $\kappa$-small category.

Note that, at least in the case $\kappa = \omega$, the conditions of the proposition are much weaker than $I$ being $\omega$-small, that is finite. For example, any finitely generated category can be shown to satisfies these conditions. I do not know if for $\kappa$ uncountable there are such example of non-$\kappa$-small categories satisfying these conditions. We refer to [8] for general material about ends.

Proof. The equivalence of conditions (1) and (2) is immediate because of the natural isomorphism:

$$\int_I A(x, x) \simeq \operatorname{Nat}(\operatorname{Hom}(x, y), A(x, y))$$

And the fact that Hom being $\kappa$-presentable means that the functor $\operatorname{Nat}(\operatorname{Hom}(x, y), \_)$ preserve $\kappa$-filtered colimits. Condition (2) implies (3) because of the expression of the morphism in the category of functors $A^I$ as:

$$\operatorname{Hom}_{A^I}(F, G) \simeq \int_{i \in I} \operatorname{Hom}_A(F(i), G(i))$$

Hence given any filtered diagram $(G_j)_{j \in J}$ and $F : I \to A_\kappa$ a functor, we have an isomorphism

$$\begin{array}{rcl} \operatorname{Hom}_{A^I}(F, \operatorname{Colim}_j G_j) & \simeq & \int_{i \in I} \operatorname{Hom}_A(F(i), \operatorname{Colim}_j G_j(i)) \\ & \simeq & \int_{i \in I} \operatorname{Colim}_j \operatorname{Hom}_A(F(i), G_j(i)) \\ & \simeq & \operatorname{Colim}_j \int_{i \in I} \operatorname{Hom}_A(F(i), G_j(i)) \\ & \simeq & \operatorname{Colim}_j \operatorname{Hom}_{A^I}(F, G_j) \end{array}$$

showing that $F$ is indeed $\kappa$-presentable.

The implication $(3) \Rightarrow (4)$ is tautological, and finally $(4) \Rightarrow (1)$ follows from the identification

$$\operatorname{Fun}(I, \mathbf{Sets}^{I^{\mathrm{op}}}) \simeq \operatorname{Fun}(I^{\mathrm{op}} \times I, \mathbf{Sets}).$$

The category $\mathbf{Sets}^{I^{\mathrm{op}}}$ is locally $\kappa$-presentable, with the representable object being $\kappa$-presentable (this holds for any $\kappa$), hence by condition (4), the Yoneda embeddings $I \to \mathbf{Sets}^{I^{\mathrm{op}}}$ is a $\kappa$-presentable object of this functor category, and through the equivalence above, this corresponds to the functor $\operatorname{Hom} : I^{\mathrm{op}} \times I \to \mathbf{Sets}$, hence concluding the proof.

Finally, if $I$ is a $\kappa$-small category, then the end involved in (2) can be rewritten as a limit indexed by the twisted arrow category of $I$, which is a $\kappa$-small limits, and hence it preserves $\kappa$-filtered colimits.

5

We also mention the following corollary of Proposition 2.1, which will be useful in the proof of Theorem 1.3 later, and is also interesting in its own right. This is directly inspired by proposition 8.8.2 of [4].

**2.2 Corollary.** *Let $I$ be an essentially $\kappa$-small category, or more generally a category satisfying the equivalent conditions of Proposition 2.1, then the functor*

$$E_{\mathcal{C},\kappa}^I : \text{Ind}_\kappa(C^I) \rightarrow \text{Ind}_\kappa(C)^I$$

*is fully faithful.*

*Proof.* Let $X$ and $Y$ be two objects of $\text{Ind}_\kappa(C^I)$, we write them as $\kappa$-directed colimits, $X = \text{Colim } X_i$ and $Y = \text{Colim } Y_j$ of diagrams in $C^I$. In the category $\text{Ind}_\kappa(C^I)$ we have

$$\begin{aligned} \text{Hom}(X, Y) &= \text{Hom}(\underset{i}{\text{Colim }} X_i, \underset{j}{\text{Colim }} Y_j) \\ &= \underset{i}{\text{Lim}} \text{Hom}(X_i, \underset{j}{\text{Colim }} Y_j) \\ &= \underset{i}{\text{Lim}} \underset{j}{\text{Colim}} \text{Hom}(X_i, Y_j) \end{aligned}$$

as the $X_i$ are $\kappa$-presentable in $\text{Ind}_\kappa(C^I)$. In the category $\text{Ind}_\kappa(C)^I$ we have

$$\begin{aligned} \text{Hom}(E_{\mathcal{C},\kappa}^I(X), E_{\mathcal{C},\kappa}^I(Y)) &= \text{Hom}(\underset{i}{\text{Colim }} E_{\mathcal{C},\kappa}^I(X_i), \underset{j}{\text{Colim }} Y_j) \\ &= \underset{i}{\text{Lim}} \text{Hom}(X_i, \underset{j}{\text{Colim }} Y_j) \\ &= \underset{i}{\text{Lim}} \underset{j}{\text{Colim}} \text{Hom}(X_i, Y_j) \end{aligned}$$

where we have used that the functor $E$ preserves $\kappa$-directed colimits by construction, and that by Proposition 2.1 the $X_i \in C^I$ are $\kappa$-presentable objects in $\text{Ind}_\kappa(C)^I$. This concludes the proof as one easily see by functoriality of the isomorphisms above that the identification $\text{Hom}(X, Y) = \text{Hom}(E_{\mathcal{C},\kappa}^I(X), E_{\mathcal{C},\kappa}^I(Y))$ we obtained is induced by the action of $E_{\mathcal{C},\kappa}^I$. $\square$

## 2.1 Proof of (L1) or (L2) $\Rightarrow$ (L3)

We fix $I$ for which the equivalent conditions (L1) and (L2) of Theorem 1.2 holds. We will show that $I$ is $\kappa$-small. We first have

**2.3 Lemma.** *Any category $I$ satisfying conditions (L1) or (L2) of Theorem 1.2 is locally $\kappa$-small, that is has $\kappa$-small Hom sets.*

*Proof.* We apply condition (L1) to the category **Sets**, whose $\kappa$-presentable objects are the $\kappa$-small sets. It follows that for every $x \in I$ the representable functor

$$\begin{aligned} I &\rightarrow \quad \textbf{Sets} \\ y &\mapsto \quad \text{Hom}(x, y) \end{aligned}$$

can be written as a $\kappa$-filtered colimit of functors $I \rightarrow \textbf{Sets}_\kappa$. In particular, there exists a functor $A : I \rightarrow \textbf{Sets}_\kappa$ and a natural transformation $\lambda_y : A(y) \rightarrow \text{Hom}(x, y)$, such that the identity functor $x \rightarrow x$ can be written as $\lambda_x(e)$ for $e \in A(x)$. But it then follows that for every arrow $p : x \rightarrow y$, we have $\lambda_y(pe) = p\lambda_y(e) = p \circ \text{Id}_x = p$, hence $A(y) \rightarrow \text{Hom}(x, y)$ is surjective, and hence $\text{Hom}(x, y)$ is a $\kappa$-small set for all $x, y \in I$. $\square$

6

We can now conclude the proof of this implication with:

**2.4 Lemma.** *Any category I satisfying conditions (L1) or (L2) of Theorem 1.2 is essentially $\kappa$-small.*

*Proof.* We have seen in Lemma 2.3 that $I$ is locally $\kappa$-small. $I$ also satisfies the last (hence all) condition of Proposition 2.1. Hence the functor $\operatorname{Hom}: I^{\mathrm{op}} \times I \to \mathbf{Sets}$ is $\kappa$-presentable. In general, given a $\kappa$-presentable object $X$ of a functor category $\mathbf{Sets}^K$, one can show that there is a $\kappa$-small family of elements $a_x \in X(k_x)$ such that every element of $X$ is the image of one of $a_x$ by the functoriality of $X$. Indeed each such family defines a subobject of $X$ and together they form a $\kappa$-filtered family of subobjects of $X$, so if $X$ is $\kappa$-presentable, then one of these subobjects is equal to $X$.

In our case, it means that there exists a $\kappa$-small set of arrows $f_x: a_x \to b_x \in I$ for $x \in X$ such that every arrow $g$ of $I$ can be factored through one of these as $g = u f_x v$ for some $x \in X$. In particular, for each object $y \in I$, we have two arrows $u, v$ such that $Id_y = u f_x v$, which implies that $y$ is a retract of $a_x$ (as well as of $b_x$). The category $I$ being locally $\kappa$-small, the full subcategory of the $a_x$ is a $\kappa$-small category $A$ and we just showed that $I$ identifies with a full subcategory of the Cauchy completion of $A$, hence is an essentially $\kappa$-small category, as the Cauchy completion of a $\kappa$-small category can be constructed as a $\kappa$-small category. $\square$

## 2.2 Proof of (L3) $\Rightarrow$ (L1)

We fix $A$ a locally $\kappa$-presentable category and $I$ a $\kappa$-small category. We will show condition (L1), i.e. that $A^I$ is also locally $\kappa$-presentable with its $\kappa$-presentable objects being the functors taking values in the full subcategory $A_\kappa$ of $\kappa$-presentable objects of $A$. Note that by Proposition 2.1, as $I$ is $\kappa$-small, the functors $I \to A_\kappa$ are indeed $\kappa$-presentable objects of $A^I$.

The evaluation functor $ev_i: A^I \to A$ (for $i \in I$) have left adjoints $F_i: A \to A^I$ than can be expressed as

$$F_i(X) := \left( j \mapsto \coprod_{\operatorname{Hom}_I(i,j)} X \right) \in A^I.$$

In particular, as the category $I$ is $\kappa$-small this coproduct is $\kappa$-small and hence if $X \in A_\kappa$, then $F_i(X) \in (A_\kappa)^I$. We have that for any $U \in A^I$, $\operatorname{Hom}(F_i(X), U) = \operatorname{Hom}(X, ev_i(U))$, so it follows that an arrow $f: U \to V$ in $A^I$ is an isomorphism if and only if for each $X \in A_\kappa$ and each $i \in I$ we have that

$$\operatorname{Hom}(F_i(X), U) \to \operatorname{Hom}(F_i(X), V)$$

is an equivalence. The following lemma, applied to the cocomplete category $\mathcal{A}^I$ and to $\mathcal{C} = (\mathcal{A}_\kappa)^I$ then concludes the proof:

**2.5 Lemma.** *Let $\mathcal{A}$ be a cocomplete category and let $\mathcal{C} \subset \mathcal{A}$ be a full subcategory of $\mathcal{A}$ such that:*

(1) \(\mathcal{C}\) is closed under \(\kappa\)-small colimits in \(\mathcal{A}\).
(2) Every object of \(\mathcal{C}\) is \(\kappa\)-presentable in \(\mathcal{A}\).

7

(3) For any arrow $f : U \rightarrow V$, if for all $c \in \mathcal{C}$, $\operatorname{Hom}(c, f) : \operatorname{Hom}(c, U) \rightarrow \operatorname{Hom}(c, V)$ is a bijection, then $f$ is an isomorphism.

Then, $\mathcal{A}$ is locally $\kappa$-presentable and up to equivalence, $\mathcal{C}$ is the category of $\kappa$-presentable objects of $\mathcal{A}$.

Proof. This is essentially the definition of a locally presentable categories, depending on the reference. We just briefly recall the argument: for any object $X \in \mathcal{A}$, we let

$$Y = \operatorname{Colim}_{\substack{c \rightarrow X \\ c \in \mathcal{C}}} c,$$

as $\mathcal{C}$ has all $\kappa$-small colimits, this is a $\kappa$-filtered colimit. As every object $d \in \mathcal{C}$ is $\kappa$-presentable we have that $\operatorname{Hom}(d, Y) = \operatorname{Colim}_{c \rightarrow X} \operatorname{Hom}(d, c) = \operatorname{Hom}(d, X)$, hence the last condition implies that the canonical map $Y \rightarrow X$ is an isomorphism. So, $\mathcal{C}$ is a dense subcategory of $\kappa$-presentable objects, hence $\mathcal{A}$ is locally $\kappa$-presentable. Finally, if $X$ is a $\kappa$-presentable object then as $X$ is a $\kappa$-directed colimits of objects of $\mathcal{C}$, then $X$ is a retract of an object in $\mathcal{C}$, and as $\mathcal{C}$ has all $\kappa$-small colimits, it is closed under retracts, so that $X$ is isomorphic to an object of $\mathcal{C}$. □

### 3 Proof of Theorem 1.3.

The equivalence between condition (A2) and condition (A3) of Theorem 1.3 follows immediately from Proposition 1.1 and the remarks right after its proof. The implication (A1) $\Rightarrow$ (A2) is tautological, so we only need to show (A2) $\Rightarrow$ (A4) and (A4) $\Rightarrow$ (A1). But before this, we need to discuss the notion of well-founded categories which appear in condition (A4).

#### 3.1 Well-founded categories

The class **Ord** of all ordinal is seen as a (large) category with a single arrow from $\beta \rightarrow \gamma$ if $\gamma \leqslant \beta$. Any ordinal $\alpha$ is seen as the small full subcategory $\alpha \subset \mathbf{Ord}$ of all ordinals $\beta < \alpha$.

We first need to introduce the following construction, which plays a central role both in the notion of well-founded categories and latter in the proof of Theorem 1.3.

**3.1 Construction.** Given $I$ a category and $\alpha$ either an ordinal or the large category **Ord** of all ordinal, we denote by $I^{(\alpha)}$ the non-full subcategory of $I \times \alpha$ which contains all the object of $I \times \alpha$ and in which the morphisms are:

1. (1) All arrows $(x, \beta) \rightarrow (y, \gamma)$ in $I \times \alpha$ if $\beta < \gamma$.
2. (2) Only the identity arrow $(x, \beta) \rightarrow (x, \beta)$.

The projection $I \times \alpha \rightarrow I$ restrict to a functor $I^{(\alpha)} \rightarrow I$ which we call the canonical functor.

It should be noted that the construction $I \mapsto I^{(\alpha)}$ is not functorial in the bicategorical sense, but only in a 1-categorical sense, as it explicitly involve the set of objects of $I$. This construction does not respect the “equivalence

8

principle” in the sense that an equivalence of category $I \simeq J$ does not imply that $I^{(\alpha)} \simeq J^{(\alpha)}$.

A binary relation $R$ on a set $X$ is said to be well-founded if there is no infinite chain $x_1, \dots, x_n, \dots$ in $X$ such that $x_{n+1}Rx_n$ for all $n$. Equivalently, if the only subset $S \subset X$ satisfying $(\forall y, yRx \Rightarrow y \in S) \Rightarrow x \in S$ is $S = X$. A poset is said to be well-founded if the relation $<$ defined as $x \leqslant y$ and $x \neq y$ is well-founded. For example ordinals are well-founded as posets, and up to isomorphisms they are the unique well-founded totally ordered sets.

A functor $F : \mathcal{C} \to \mathcal{D}$ is said to be *identity-reflecting* if for every arrow $f$, $F(f)$ is an identity arrow implies that $f$ is an identity arrow. Note that this notion also breaks the equivalence principle: a functor equivalent to an identity-reflecting functor doesn't have to be identity-reflecting.

The posetal reflection of a category $I$, is the universal poset with a functor from $I$. One start with the relation on the set of objects of $I$ defined by $x \leqslant y :=$ “There exists an arrow $x \to y$” which is transitive and reflective and then one quotient the set of objects by the equivalence relation $x \leqslant y$ and $y \leqslant x$ to make into a poset.

### 3.2 Lemma. For a category $I$ the following conditions are equivalent:

1. (1) *The functor from $I$ to its posetal reflection is identity-reflecting.*
2. (2) *The category $I$ has no non-identity isomorphisms or endomorphisms.*

*Proof.* Any isomorphism or endomorphism is sent to an identity in the posetal reflection of $I$, so the implication $(1) \Rightarrow (2)$ is clear. We hence assume that $I$ has no non-identity endomorphisms or isomorphisms. Two objects $x, y$ of $I$ become identified in the posetal reflection of $I$ if and only if there are maps $f : x \to y$ and $g : y \to x$, but then the composite $f \circ g$ and $g \circ f$ are endomorphisms, hence identity, hence $f$ and $g$ are isomorphisms, and hence $x = y$. It follows that the map from $I$ to its posetal reflection is bijective on objects, and as $I$ has no non-identity endomorphisms this makes it identity-reflecting. $\square$

### 3.3 Proposition. For a category $I$, the following conditions are equivalents:

1. (SW1) *There are no identity-reflecting functors $\omega^{\circ p} \to I$.*
2. (SW2) *The relation $x < y$ on objects of $I$ defined by “there exists a non-identity arrow $x \to y$” is well-founded.*
3. (SW3) *The category $I$ has no non-identity isomorphisms or endomorphisms and its posetal reflection is a well-founded poset.*
4. (SW4) *There is an identity-reflecting functor $\mathcal{C} \to \mathbf{Ord}$.*
5. (SW5) *The canonical functor $I^{(\mathbf{Ord})} \to I$ admits a section (up to equality)*

*A category satisfying these conditions is said to be strictly well-founded.*

9

Proof. The equivalence between (SW1) and (SW2) is immediate as the functors mentioned in (SW1) are exactly the downward chains for the relation mentioned in (SW2).

(SW2) $\Rightarrow$ (SW3): indeed, any isomorphisms or endomorphisms in $I$ would allow to obtain either a $x$ such that $x < x$ or $x, y$ such that $x < y$ and $y < x$ which is impossible in a well-founded relation, and if there are no isomorphisms or endomorphisms, then the posetal reflection is the set of objects with the relation of the point (SW2).

(SW3) $\Rightarrow$ (SW4) Every well-founded-poset admits a functor to **Ord** which is identity-reflecting (e.g. defined by well-founded induction as $v(x) = \sup_{y<x} v(y)^+$) so the implication follows by Lemma 3.2.

(SW4) $\Rightarrow$ (SW5). Given $F: I \to \mathbf{Ord}$ an identity-reflecting functor, then the functor $(Id, F): I \to I \times \mathbf{Ord}$ is a section of the first projection and takes values in $I^{(\mathbf{Ord})}$.

(SW5) $\Rightarrow$ (SW1): a section of $I^{(\mathbf{Ord})} \to I$ is automatically identity reflecting, so the existence of such section implies that there is an identity reflecting functor $I \to \mathbf{Ord}$ which clearly contradicts the existence of an identity reflecting functor $\omega^{\mathrm{op}} \to I$ as there is no such functor $\omega^{\mathrm{op}} \to \mathbf{Ord}$.

### 3.4 Proposition. For a category $I$, the following conditions are equivalents

(W1) I has no non-identity endomorphisms and it admits a conservative functor to Ord.
(W2) I has no non-identity endomorphisms and its posetal reflection is well-founded.
(W3) Every skeleton of \( I \) is a strictly well-founded category.
\((W_{4})\) I is equivalent to a strictly well-founded category.
(W5) The canonical functor \( I^{(\alpha)} \to I \) admits a section up to natural isomorphisms.
(W6) The identity functor on \( I \) is a retract of a functor that can be factored as a functor \( I \to I^{(\alpha)} \) followed by the canonical functor \( I^{(\alpha)} \to I \).

A category satisfying these equivalent conditions will be said to be Well-founded.

Condition (W6) may seem a little strange - the only reason it is here is because this characterization will be used in the next subsection to show the implication $(A2) \Rightarrow (A4)$ of Theorem 1.3.

Proof. (W1) $\Rightarrow$ (W2). Such a conservatif functor factors into a conservatif functor from the posetal reflection of $I$ to **Ord**, which implies that this posetal reflection has no infinite strictly decreasing chains, hence is well-founded.

(W2) $\Rightarrow$ (W3). This follows immediately from point (SW3) of Proposition 3.3: indeed in a skeleton all isomorphisms will be endomorphisms, and hence a skeleton of a category satisfying (W2), will have non-identity endomorphisms and isomorphisms and a well-founded posetal reflection, so satisfy condition (SW3) of Proposition 3.3.

10

(W3) $\Rightarrow$ (W4) is tautological.

(W4) $\Rightarrow$ (W5). The construction $I^{(\text{Ord})}$ is not a functor in the 2-categorical or bicategorical sense, but it is functorial in the 1-categorical sense nonetheless. So given an equivalence $F: A \rightarrow I$ with $A$ a strictly well-founded category, we get a commutative square:

$$\begin{array}{ccc} A^{(\text{Ord})} & \xrightarrow{F^{(\text{Ord})}} & I^{(\text{Ord})} \\ \downarrow{\pi_A} & & \downarrow{\pi_I} \\ A & \xrightarrow{F} & I \end{array}$$

By point (SW5) of Proposition 3.3, the left functor $\pi_A$ has a section $s$ (up to equality) and the bottom functor $F$ is an equivalence (so it has an inverse up to is morphisms), so composing $F^{(\text{Ord})}sF^{-1}$ gives a functor $I \rightarrow I^{(\alpha)}$ such that if one post-compose it by $\pi_I$ we get $\pi_I F^{(\text{Ord})}sF^{-1} = F\pi_A sF^{-1} = FF^{-1} \simeq \text{Id}_I$ hence the result.

(W5) $\Rightarrow$ (W6) is tautological.

(W6) $\Rightarrow$ (W1). We get a functor $F: I \rightarrow \text{Ord}$ by composing the functor $I \rightarrow I^{(\text{Ord})}$ with the projection $I^{(\text{Ord})} \subset I \times \text{Ord} \rightarrow \text{Ord}$. Let $f$ be any arrow such that $F(f)$ is an identity. As the only arrows in $I^{(\text{Ord})}$ sent to identities in $\text{Ord}$ are identities, it follows that the image of $f$ is already an identity arrow in $I^{\text{Ord}}$, hence $f$ is a retract of an identity arrow in $I$, so it has to be an isomorphism. This proves that the functor to $\text{Ord}$ is conservative. If we further assume that $f$ is an endomorphism of an object, then the same argument shows that $f$ is a retract of an identity, with the same retraction on each side, which forces $f$ to be an identity arrow, hence this concludes the proof. $\square$

### 3.2 Proof of (A2) $\Rightarrow$ (A4)

We fix $I$ a category such that for all Cauchy complete category $\mathcal{C}$, the functor $E_{\mathcal{C},\kappa}^I: \text{Ind}_\kappa(\mathcal{C}^I) \rightarrow \text{Ind}_\kappa(\mathcal{C})^I$ is an equivalence. It is in particular an equivalence for all category $\mathcal{C}$ having $\kappa$-small colimits, so by Theorem 1.2 the category $I$ is $\kappa$-small.

We then take $\mathcal{C} = I^{(\kappa)}$. For each $x \in I$, we consider the object $E_x \in \text{Ind}_\kappa$ defined as follows:

$$E_x = \underset{\alpha < \kappa}{\text{Colim}}(x, \alpha)$$

As $\kappa$ is assumed to be a regular cardinal (which we consider as an ordinal here), the poset $\kappa$ has all $\kappa$-small join and hence is $\kappa$-directed. As a functor $\mathcal{C}^{\text{op}} \rightarrow \text{Sets}$, $E_x$ can be described as:

$$E_x(y, \alpha) = \text{Hom}_I(y, x)$$

So this clearly constitutes a functor $E: I \rightarrow \text{Ind}_\kappa(\mathcal{C})$. It should also be noted that the functor $\text{Ind}_\kappa(\pi_I): \text{Ind}_\kappa(I^{(\alpha)}) \rightarrow \text{Ind}_\kappa(I)$ sends the objects $E_x$ to the object $x$ itself as the all the $(x, \alpha)$ are sent to $x$ and hence the colimit defining $E_x$ becomes trivial in $\text{Ind}_\kappa(I)$. So that the composite $\text{Ind}_\kappa(\pi_I) \circ E: I \rightarrow \text{Ind}_\kappa(I)$ identifies with the canonical functor $I \rightarrow \text{Ind}_\kappa(I)$.

As we are assuming condition (A2) of Theorem 1.3 and the category $\mathcal{C} = I^{(\kappa)}$ is Cauchy complete (it has no non-identity idempotent), we can hence find a

11

$\kappa$-directed family of functors $F^j : I \rightarrow I^{(\kappa)}$ such that $E = \operatorname{Colim}_j F^j$ in the category of functors $I \rightarrow \operatorname{Ind}_{\kappa}(I^{(\kappa)})$.

$\operatorname{Ind}_{\kappa}(\pi_I)$ preserves $\kappa$-filtered colimit, so we also have that

$$\operatorname{Colim}_j \operatorname{Ind}_{\kappa}(\pi_I) F^j \simeq \operatorname{Ind}_{\kappa}(\pi_I) E$$

Identify with the canonical functor $I \rightarrow \operatorname{Ind}_{\kappa}(I)$. Now, applying our assumption (A2) to (the Cauchy completion of) $I$, we see that this implies that the canonical functor $I \rightarrow \operatorname{Ind}_{\kappa}(I)$ is a $\kappa$-presentable object of the category of all such functor, and hence because of the previous colimit it has to be a retract of one of the functors $\operatorname{Ind}_{\kappa}(\pi_I)F^j$, but then all the functors involved actually takes values in $I$ and hence we have shown that the identity of $I$ is a retract of $\pi_I \circ F^j$ for some $j$, which is exactly condition (W6) of Proposition 3.4. Hence proving that $I$ is well-founded.

### 3.3 Proof of (A4) $\Rightarrow$ (A1)

We are now showing that if $I$ is well-founded and $\kappa$-small and $\mathcal{C}$ is any category, then $E_{\mathcal{C},\kappa}^I : \operatorname{Ind}_{\kappa}(\mathcal{C}^I) \rightarrow \operatorname{Ind}_{\kappa}(\mathcal{C})^I$ is an equivalence. The strategy here is to show first that, for $I$ a $\kappa$-small category and $\alpha < \kappa$ an ordinal, the functor

$$E_{\mathcal{C},\kappa}^{I^{(\alpha)}} : \operatorname{Ind}_{\kappa}(\mathcal{C}^{I^{(\alpha)}}) \rightarrow \operatorname{Ind}_{\kappa}(\mathcal{C})^{I^{(\alpha)}}$$

is an equivalence, which we achieve by induction on $\alpha$, and then we exploit that when $I$ is well-founded it is a retract of one of the $I^{(\alpha)}$ to conclude the proof.

We start with the following proposition:

**3.5 Proposition.** *Let $\alpha < \kappa$ any $\kappa$-small ordinal. Let $\mathcal{C}_{\bullet} : \alpha^{op} \rightarrow \mathbf{Cat}$ be a tower of categories with the property that for each $\gamma < \alpha$ the functor*

$$\mathcal{C}_{\gamma} \rightarrow \operatorname{Lim}_{\beta < \gamma} \mathcal{C}_{\beta}$$

*is (equivalent to a) cartesian fibration. Then the limit $\operatorname{Lim}_{\beta < \alpha} \mathcal{C}_{\beta}$ is preserved by $\operatorname{Ind}_{\kappa}$.*

**3.6 Remark.** Here by limits, we mean pseudo-limits. As the $\operatorname{Ind}_{\kappa}$ functor is only well defined up to equivalence, asking for the preservation of strict limits does not really make sense. Because of this, it does not make sense either to ask the comparison functors in the proposition to be Grothendieck cartesian fibration in the strict sense, as they are only well defined up to equivalences of categories. This is why we only require that they are equivalent to cartesian fibration (equivalently, are Street fibrations). Of course, one could take all limits to be strict limits, and then one could ask these functors to be Grothendieck fibrations. As Grothendieck fibrations are in particular isofibrations, these strict limits would be equivalent to the corresponding pseudo-limits. The $\operatorname{Ind}_{\kappa}$ functor would then preserves the strict limit up to equivalences of categories.

*Proof.* We fix $\alpha$ a $\kappa$-small ordinal and

$$\mathcal{C}_0 \leftarrow \mathcal{C}_1 \leftarrow \cdots \leftarrow \mathcal{C}_{\gamma} \leftarrow \dots$$

12

a sequence of categories indexed by $\alpha^{\mathrm{op}}$, whose transition maps are cartesians fibrations. We need to show that the inclusion

$$\operatorname*{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma} \subset \operatorname*{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$$

identifies the right-hand side with the $\operatorname{Ind}_{\kappa}$ completion of the left-hand side. The proof has three parts: first one shows that the objects of $\operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma}$ are $\kappa$-presentable in the right hand side, mostly using the same sort of argument as in Proposition 2.1, the second step is to show that the functor

$$E: \operatorname{Ind}_{\kappa} \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma} \to \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$$

is fully faithful, using the exact same argument as in Corollary 2.2, and finally the third step is to show that this functor is essentially surjective, that is that every object of $\operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$ is a $\kappa$-filtered colimits of objects of $\operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma}$. Here the argument is to show that for all $Y$ in the limits, the diagram of all the $X \to Y$ with $X \in \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \mathcal{C}_{\gamma}$ is $\kappa$-filtered and has colimit $Y$.

For the first part, we observe that in the limit $\operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$, all the transition functors preserve $\kappa$-filtered colimits, so all $\kappa$-filtered colimits are computed componentwise. The Hom set in the limits can be written as a $\kappa$-small limit

$$\operatorname{Hom}(X, Y) = \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Hom}(X_{\gamma}, Y_{\gamma}).$$

So, if for all $\gamma$, the objects $X_{\gamma}$ is in $\mathcal{C}_{\gamma}$, and hence $\kappa$-presentable, then each individual Hom functor preserves $\kappa$-filtered colimits in the second variable, and the limits being $\kappa$-small, it comutes to $\kappa$-filtered colimits, hence $\operatorname{Hom}(X, \cdot)$ preserves $\kappa$-filtered colimits. So that $(X_{\gamma}) \in \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$ is $\kappa$-presentable.

For the second part, we can just run the exact same argument as in Corollary 2.2. The functor $E$ preserves $\kappa$-filtered colimits by construction, and so we can do the exact same computation as in the proof of Corollary 2.2 to conclude that the functor $E$ is fully faithful.

Moving to the third part, we show that for any

$$Y = (Y_{\gamma})_{\gamma \in \alpha^{\mathrm{op}}} \in \operatorname{Lim}_{\gamma \in \alpha^{\mathrm{op}}} \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$$

the category of $X \to Y$ with $X_{\gamma} \in \mathcal{C}_{\gamma}$ is $\kappa$-filtered. So let $X^{(i)}$ be a $\kappa$-small diagram of such objects. We construct a cocone for it, that is a factorization $X^{(i)} \to E \to Y$ where all $E_{\gamma} \in \mathcal{C}_{\gamma}$ and the first arrow is natural in $i$. This is done by induction on $\gamma$. Indeed assuming such an $E_{\beta}$ has been constructed for all $\beta < \gamma$, that is we have our (natural) factorization $X^{(i)} \to E \to Y$ in the category $\operatorname{Lim}_{\beta < \gamma} \mathcal{C}_{\beta}$. First, as $Y_{\gamma} \in \operatorname{Ind}_{\kappa}(\mathcal{C}_{\gamma})$, exists an object $E_{\gamma}^{0} \in \mathcal{C}_{\gamma}$ that factors the cocone $X_{\gamma}^{(i)} \to E_{\gamma}^{0} \to Y_{\gamma}$. The functor $\pi: \operatorname{Ind}_{\kappa} \mathcal{C}_{\gamma} \to \operatorname{Lim}_{\beta < \gamma} \operatorname{Ind}_{\kappa} \mathcal{C}_{\beta}$ preserves $\kappa$-filtered colimits, so we can further “enlarge” $E_{\gamma}^{0}$ so that its image $\pi(E_{\gamma}^{0})$ in this limit also factors the already existing map

$$X^{(i)} \to E \to \pi(E_{\gamma}^{0}) \to Y$$

while making sure that the composite $X^{(i)} \to E \to \pi(E_{\gamma}^{0})$ identifies with the image under $\pi$ of the cocone structure $X_{\gamma}^{(i)} \to E_{\gamma}^{0}$. Finally, we construct $E_{\gamma}$

13

as a cartesian lift of $E \rightarrow \pi(E_\gamma^0)$ to a map $E_\gamma \rightarrow E_\gamma^0$, and easily check that $E_\gamma$ has all the properties needed to extend $E$.

Finally, we show that any $Y \in \text{Lim}_{\gamma \in \alpha^\infty} \text{Ind}_\kappa(\mathcal{C}_\gamma)$ is indeed the colimits of this $\kappa$-filtered diagram. $\kappa$-filtered colimits being computed componentwise it is enough to check that for each $V \in \mathcal{C}_\gamma$ and any maps $V \rightarrow Y_\gamma$, the map can be factored as $V \rightarrow X_\gamma \rightarrow Y_\gamma$ where $X \rightarrow Y$ is a map in the limits with $X \in \text{Lim}_{\gamma \in \alpha^\infty} \mathcal{C}_\gamma$, and that given two such factorizations, they can be equalized by some larger $X' \rightarrow Y$. This can be achieved by exactly the same construction as above, by just adding one step: when constructing $E_\gamma^0$, one can make it so that (depending on the case) either the map $X_\gamma \rightarrow Y_\gamma$ factors through $E_\gamma^0 \rightarrow Y_\gamma$ or that the two maps $V \Rightarrow X_\gamma$ are equalized by $E_\gamma^0$, and then proceed with constructing $E_\gamma^0 \rightarrow E_\gamma$ in the same way. And this concludes the proof. $\square$

**3.7 Lemma.** *Let $C$ be any category and $A \subset B$ be a sieve inclusion. That is $A$ is a full subcategory of $B$ such that for $f : b \rightarrow a$ with $a \in A$ we have $b \in B$. Then restriction functor $C^B \rightarrow C^A$ is a cartesian fibration.*

*Proof.* We omit the details. The central observation is that given $F : B \rightarrow C$, $E : A \rightarrow C$, and $\lambda : E \rightarrow F|_B$ a cartesian lift of $\lambda$ is obtained by considering $F' : B \rightarrow C$ to be defined as

$$F'(b) = \begin{cases} E(b) & \text{if } b \in A. \\ F(b) & \text{Otherwise.} \end{cases}$$

with the functoriality of $F'$ being given by the functoriality of $E$ and $F$ respectively for the arrows whose source and target are either both in $A$ or both outside of $A$, for the arrows $f : a \rightarrow b$ with $a \in A$, and $b \notin A$, by

$$E(a) \xrightarrow{\lambda} F(a) \xrightarrow{F(f)} F(b)$$

and as $A$ is a sieve, there are no arrows going in the other direction. $\square$

**3.8 Proposition.** *Let $\mathcal{C}$ be any category, $I$ be a $\kappa$-small category and $\alpha < \kappa$ an ordinal then*

$$E_{\mathcal{C},\kappa}^{I(\alpha)} : \text{Ind}_\kappa\left(\mathcal{C}^{I(\alpha)}\right) \rightarrow \text{Ind}_\kappa(\mathcal{C})^{I(\alpha)}$$

*is an equivalence.*

*Proof.* We proceed by induction on $\alpha$, that is we assume the result is true for all $\beta < \alpha$. In the case of $\alpha = 0$, the category $I^{(\alpha)}$ is the discrete category on the set $X$ of objects of $I$, which is in particular a $\kappa$-small set. It is then easy to check that in this case the map:

$$E_{\mathcal{C},\kappa}^X : \text{Ind}_\kappa\left(\mathcal{C}^X\right) \rightarrow \text{Ind}_\kappa(\mathcal{C})^X$$

is an equivalence, which gives the case $\alpha = 0$.

If $\alpha = \beta^+$ is a successor ordinal, we show that $E_{\mathcal{C},\kappa}^{I(\alpha)}$ is an equivalence following a strategy similar to the proof of Proposition 3.5. First one can apply Corollary 2.2 to show that it is fully faithful. So we only need to show that it is essentially surjective, that is that every object $Y \in \text{Ind}_\kappa(\mathcal{C})^{I(\alpha)}$ is a $\kappa$-directed colimit of objects in $\mathcal{C}^{I(\alpha)}$. For this we will proceed in two steps: we first show that the slice $\mathcal{C}^{I(\alpha)}/Y$ is a $\kappa$-filtered category and then that $Y$ is its colimits. In

14

both cases a key observation is that as the result is assumed to be true for $\beta$, both these claims are true when $\beta$ is replaced by $\alpha$.

So we consider a $\kappa$-small diagram $X^i \rightarrow Y$ in $\mathcal{C}^{I^{(\alpha)}}/Y$ and we will show it admits a cocone. First, by our induction hypothesis, the restriction to $I^{(\beta)}$ has a cocone $X^i|_{I^{(\beta)}} \rightarrow E \rightarrow Y|_{I^{(\beta)}}$. We only need to extend $E$ to the object of the form $(\alpha, i) \in I^{(\alpha)}$, endowed with maps $E(\alpha, i) \rightarrow Y(\alpha, i)$, and all the appropriate maps from the $E(\beta, i) \rightarrow E(\alpha, i)$ and maps $X^i(\alpha, i) \rightarrow E(\alpha, i)$ such that composites, for example $E(\beta, i) \rightarrow E(\alpha, i) \rightarrow Y(\alpha, i)$, are the correct maps. This can be summed up as the question of finding a cocone for a certain $\kappa$-small diagram in $\mathcal{C}/Y(\alpha, i)$, hence we can build these objects as $Y(\alpha, i) \in \text{Ind}_\kappa(\mathcal{C})$.

Finally, similarly to the proof of Proposition 3.5, in order to show that $Y$ is the colimits of $\mathcal{C}^{I^{(\alpha)}}/Y$, it is enough to show that for all $\gamma \leqslant \alpha$ and for each arrow $V \rightarrow Y(\gamma, i)$ for $V \in \mathcal{C}$, this arrow can be factored as $V \rightarrow X(\gamma, i) \rightarrow Y(\gamma, i)$ for $X \in \mathcal{C}^I/Y$, and that any two such factorizations are equalized by some $X \rightarrow X'$ in $\mathcal{C}^I/Y$. But this is easily done by the exact same argument: One first builds the restriction of $X$ to $I^{(\beta)}$ by the induction hypothesis and then we extend $X$ to $I^{(\alpha)}$ by finding certain cocones for $\kappa$-small diagrams in $\mathcal{C}/Y(\alpha, i)$.

We now move to that last part of the proof: $\alpha$ is a limit ordinal, then $I^{(\alpha)}$ is the union of the $I^{(\beta)}$ for $\beta \subset \alpha$, which are all sieve in $I^{(\alpha)}$. Hence

$$\mathcal{C}^{I^{(\alpha)}} = \lim_{\beta < \alpha} \mathcal{C}^{I^{(\beta)}}$$

and Lemma 3.7 immediately implies that this limit satisfies the conditions of Proposition 3.5, hence:

$$\text{Ind}_\kappa(\mathcal{C}^{I^{(\alpha)}}) \simeq \lim_{\beta < \alpha} \text{Ind}_\kappa(\mathcal{C}^{I^{(\beta)}})$$

hence by our induction hypothesis, we obtain

$$\text{Ind}_\kappa(\mathcal{C}^{I^{(\alpha)}}) \simeq \lim_{\beta < \alpha} \text{Ind}_\kappa(\mathcal{C})^{I^{(\beta)}} \simeq \text{Ind}_\kappa(\mathcal{C})^{I^{(\alpha)}},$$

which concludes the proof.

We can now prove the claimed implication:

**3.9 Proposition.** *Let $I$ be an essentially $\kappa$-small well-founded category, and $\mathcal{C}$ any category, then*

$$E_{\mathcal{C},\kappa}^I : \text{Ind}_\kappa(\mathcal{C}^I) \rightarrow \text{Ind}_\kappa(\mathcal{C})^I$$

*is an equivalence of categories.*

*Proof.* One can freely assume that $I$ is $\kappa$-small. As $I$ is well-founded, then the projection $I^{(\text{Ord})} \rightarrow I$ admits a section up to isomorphism. The composite functor $I \rightarrow I^{(\text{Ord})} \rightarrow \text{Ord}$ has a $\kappa$-small image, so it factors through an order preserving inclusion $\alpha \subset \text{Ord}$ for $\alpha$ a $\kappa$-small ordinal.

The full subcategory of objects of $I^{(\text{Ord})}$ whose image in $\text{Ord}$ is in this $\kappa$-small ordinal identifies to $I^{(\alpha)}$, and hence we have a section (up to isomorphic) of the projection $I^{(\alpha)} \rightarrow I$.

It follows that the functor $E_{\mathcal{C},\kappa}^I$ is a retract (up to natural isomorphisms) of the functor $E_{\mathcal{C},\kappa}^{I^{(\alpha)}}$, which is known to be an equivalence by Proposition 3.8, hence is itself an equivalence of category.

15

## References

[1] Jiří Adámek and Jiří Rosický. *Locally presentable and accessible categories*, volume 189. Cambridge University Press, 1994.
[2] Gregory J Bird. *Limits in 2-categories of locally presentable categories*. PhD thesis, PhD thesis, University of Sydney. Circulated by the Sydney Category theory seminar, 1984. http://maths.mq.edu.au/~street/BirdPhD.pdf.
[3] A Carboni, MC Pedicchio, and Jiří Rosický. Syntactic characterizations of various classes of locally presentable categories. *Journal of Pure and Applied Algebra*, 161(1-2):65–90, 2001.
[4] Deligne, P. and Boutot, JF and Grothendieck, A. and Illusie, L. and Verdier, JL. *Séminaire de géométrie algébrique du Bois-Marie, SGA 4 [1 over 2]: Theorie des topos et cohomologie etale des schemas*. Springer, 1973.
[5] Ivan Di Liberti and Julia Ramos González. Gabriel–Ulmer duality for topoi and its relation with site presentations. *Applied Categorical Structures*, 28(6):935–962, 2020.
[6] Simon Henry. $\text{Ind}(C^I) = \text{Ind}(C)^I$? MathOverflow. https://mathoverflow.net/q/442055 (version: 2023-03-03).
[7] Pierre-Alain Jacqmin and Zurab Janelidze. On stability of exactness properties under the pro-completion. *Advances in Mathematics*, 377:107484, 2021.
[8] Fosco Loregian. Coend calculus. *arXiv preprint arXiv:1501.02503*, 2015.
[9] Jacob Lurie. *Higher topos theory*. Number 170. Princeton University Press, 2009.
[10] Michael Makkai. Strong conceptual completeness for first-order logic. *Annals of pure and applied logic*, 40(2):167–215, 1988.
[11] Carol Vincent Meyer. *Completion of categories under certain limits*. PhD thesis, McGill University, 1983. https://library-archives.canada.ca/eng/services/services-libraries/theses/Pages/item.aspx
[12] Leonid Positselski. Notes on limits of accessible categories. *arXiv preprint arXiv:2310.16773*, 2023.
[13] Morgan Rogers. Toposes of monoid actions. *arXiv preprint arXiv:2112.10198*, 2021.

16