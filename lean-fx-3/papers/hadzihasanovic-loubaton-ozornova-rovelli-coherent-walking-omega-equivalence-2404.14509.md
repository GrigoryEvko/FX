arXiv:2404.14509v1 [math.CT] 22 Apr 2024

# A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

AMAR HADZIHASANOVIC, FÉLIX LOUBATON, VIKTORIYA OZORNOVA,
AND MARTINA ROVELLI

**ABSTRACT.** We prove that a certain $\omega$-category, which was constructed in previous work by the third and fourth author, is a model for the fully coherent walking $\omega$-equivalence. Further, appropriate truncations of it give models for the fully coherent walking $n$-equivalence for each $n \geq 1$.

## INTRODUCTION

An $\omega$-category is a type of strict categorical structure which allows for cells in each positive dimension, together with composition and identity operators, which satisfy strict axioms of associativity, unitality and interchange. When all cells are identities past dimension $n$ one refers to an $n$-category, recovering the well known instances of a set, category and 2-category, when $n = 0, 1, 2$. Both $n$-categories for $n \geq 0$ and $\omega$-categories are prominent in the literature, and are studied e.g. in [Str87, Ste04, LMW10, AM20].

Given the strictness of the axioms, examples that occur naturally in mathematical nature (such as various higher categories of cobordisms and spans, and higher Morita categories) do not generally assemble into a strict $\omega$- or $n$-category. These generally form a weak infinite-dimensional category, often referred to as an $(\infty, \infty)$-category, given that the definition of composition operators is only weakly well-defined and the axioms only hold weakly. Nevertheless, developing an understanding for strict $\omega$- and $n$-categories is crucial to tackle the study of weak $(\infty, \infty)$- and $(\infty, n)$-categories:

- » Strict $\omega$-categories often parameterize operations and interesting quantities in weak higher categories. This is the approach taken, e.g., in [Rez10, RV16, HORR23, FHM23] where strict $\omega$- or $n$-categories are used to parameterize free composites, (homotopy coherent) adjunctions, and pasting diagrams in a weak higher category.
- » Strict $\omega$-categories provide a first — and yet non-trivial — approximation of the theory of weak $(\infty, \infty)$-categories (cf. [Ver08, Gol23, Gol24]), and as such they can be used as a playground to better understand the behavior of infinite-dimensional higher categories.
- » In the theory of polygraphs, strict $\omega$-categories model higher-dimensional rewrite systems, such as those arising from presentations by generators and relations of groups, monoids, and higher algebraic structures (cf. [ABG$^{+}$23]).

For reasons discussed in [OR24], it is necessary to understand which is the intrinsic notion of sameness for two objects inside a given $n$- or $\omega$-category. This is typically expressed by requiring the existence of a 1-cell between said objects,

2020 *Mathematics Subject Classification*. 18N30; 18N20; 18N40.

1

2

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

together with other cells witnessing that the 1-cell is “reversible” in a suitably weak sense. Properties of such notion of sameness, which we refer to as $\omega$-equivalence or $n$-equivalence, have been studied e.g. in [Che07, Gur12, AL20, Had20, Ric20, cli22, FHM23, HL23, Lou23, OR24].

One can formally identify an $\omega$-category $\omega\mathcal{E}$ (resp. $n$-category $(n-1)\mathcal{E}$) that classifies $\omega$-equivalences (resp. $(n-1)$-equivalences); cf. e.g. [AL20, Remark 4.4]). For instance, for $n=1,2$ we would get, respectively, the walking isomorphism $\mathcal{I}$ and the walking equivalence $\mathcal{E}$ considered e.g. in [Lac04]. However, these known candidates are known to lack coherence as soon as $n \geq 2$. More precisely, $\omega\mathcal{E}$ (resp. $(n-1)\mathcal{E}$ for $n \geq 2$) is known to not be contractible in the model structure on the category of $\omega$-categories (resp. $n$-categories) from [LMW10].

As showcased, for instance, in [Lac02, Lac04, OR21] for the case $n=2$, it is important to have at one’s disposal contractible models of the fully coherent $(n-1)$-equivalence. When checking whether a 1-morphism inside a 2-category is an equivalence, it is sufficient to look at incoherent equivalences. However, if one wants the data witnessing an equivalence to be essentially unique, then this is encoded by a coherent equivalence, as discussed in [Lac04]. This principle was also used in [OR21] to enhance the Duskin nerve to a right Quillen functor from 2-categories to multiply marked simplicial sets. Indeed, an explicit walking coherent equivalence allows for an explicit construction for the localization of a 2-, or more generally $n$- or even $\omega$-category at a set of cells, by attaching the walking coherent equivalence at each of those cells.

For all $n > 0$, we know for abstract reasons (cf. [LMW10, §4.7]) that there must exist a contractible $\omega$-category (resp. $n$-category) with two objects, and it is shown in [ABG$^{+}$23, Proposition 20.4.5] that such $\omega$-category (resp. $n$-category) will automatically classify $\omega$-equivalences (resp. $(n-1)$-equivalences). Hence, one such $\omega$-category (resp. $n$-category) deserves to be referred to as a *fully coherent walking $\omega$-equivalence* (resp. *fully coherent walking $(n-1)$-equivalence*). For $n=1$, one can take as a model for the coherent $(n-1)$-equivalence again $\mathcal{I}$, the usual walking isomorphism, and for $n=2$ one can take $\mathcal{E}^{\text{adj}}$, the walking adjoint equivalence. For $n=3$, it is likely — yet unknown — that the 3-category bi$\mathcal{E}^{\text{adj}}$ (cf. [Gur12, §2]) is a model for the fully coherent walking 2-equivalence. No model for the fully coherent $n$-equivalence for $n > 2$ or $\omega$-equivalence is known.

In [OR24, §1.5], a candidate $\widehat{\omega\mathcal{E}}$ for the fully coherent walking $\omega$-equivalence, which is a polygraph and of finite type, was introduced by the third- and fourth-named authors. Using the theory of marked $\omega$-categories from [HL23], we show in this paper as Theorem 1.33 that $\widehat{\omega\mathcal{E}}$ is a contractible $\omega$-category. In particular, it indeed realizes the fully coherent walking $\omega$-equivalence.

**Theorem.** *The possibly coherent walking $\omega$-equivalence $\widehat{\omega\mathcal{E}}$ from [OR24, Construction 1.5.13] is indeed a model for the coherent walking $\omega$-equivalence.*

The intelligent $n$-truncation functor $\tau_{\leq n}^{\text{i}}: \omega\mathcal{C}at \rightarrow n\mathcal{C}at$ from [AM20, §1.2] is shown in [LMW10, §6] to be a left Quillen functor, and as such it preserves categorical equivalences between polygraphs. In particular, as a consequence of the theorem we also obtain that $\tau_{\leq n}^{\text{i}}\widehat{\omega\mathcal{E}}$ is a contractible $n$-category of finite type, so it realizes the fully coherent walking $(n-1)$-equivalence, for each $n > 0$:

**Corollary.** *Given $n > 0$, the intelligent truncation $\tau_{\leq n}^{\text{i}}\widehat{\omega\mathcal{E}}$ of the possibly coherent walking $\omega$-equivalence is a model for the coherent walking $n$-equivalence.*

A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

3

**Acknowledgements.** The content of this note benefited from conversations with Dimitri Ara, Lennart Meier, François Métayer, Samuel Mimram, and Alex Rice. This work started during a visit of the first-named author to MPIM Bonn, supported by the Estonian Research Council grant PSG764, and it was completed during a wonderful conference at the University of Utrecht, sponsored by NWO OCENW.KLEIN.364. The fourth-named author is grateful for support from the National Science Foundation under Grant No. DMS-2203915.

## 1. THE MODEL FOR THE COHERENT $\omega$-EQUIVALENCE

1.1. **$\omega$-categories.** We refer the reader to e.g. [LMW10, §3.2] for the notion of an $\omega$-category and $\omega$-functor. Roughly speaking, an $\omega$-category $\mathcal{D}$ consists of a set of $n$-cells $\mathcal{D}_n$ for $n \geq 0$, together with domain and codomain operators $d^+, d^- : \mathcal{D}_n \to \mathcal{D}_{n-k}$, composition operators $*_{n-k} : \mathcal{D}_n \times_{\mathcal{D}_{n-k}} \mathcal{D}_n \to \mathcal{D}_n$, and identity operators id: $\mathcal{D}_{n-k} \to \mathcal{D}_n$ for $0 < k \leq n$, satisfying strictly appropriate associativity, unitality, and interchange axioms. We follow the convention that $g *_{n-k} f$ is defined whenever $d_{n-k}^+ f = d_{n-k}^- g$. An $\omega$-functor $F : \mathcal{D} \to \mathcal{E}$ consists of an assignment $F_n : \mathcal{D}_n \to \mathcal{E}_n$ that commutes with all relevant operators.

We collect here the $\omega$-categories and constructions of such that will play a role in this paper.

- » Given $n \geq 0$, we denote by $\mathcal{C}_n$ the *walking n-cell*, a.k.a. *n-disk* and *n-globe*, which is freely generated by an $n$-cell, and we denote by $\partial \mathcal{C}_n$ its boundary, which is freely generated by two $(n-1)$-cells which have the same domain and codomain.
- » Given an $\omega$-category $\mathcal{D}$, we denote by $\mathcal{D}^\circ$ the *total dual $\omega$-category* of $\mathcal{D}$, which, roughly speaking, has the same sets of $n$-cells but swaps the domain and codomain operators. This construction is considered e.g. in [AM20, §1.8].
- » Given two $\omega$-categories $\mathcal{A}$ and $\mathcal{B}$, we denote by $\mathcal{A} \amalg \mathcal{B}$ the *disjoint union* of $\mathcal{A}$ and $\mathcal{B}$, which is defined as the categorical coproduct in $\omega \mathcal{C}at$ and has the disjoint union of the sets of $n$-cells of $\mathcal{A}$ and $\mathcal{B}$ as the set of $n$-cells.
- » The category $\omega \mathcal{C}at$ is cocomplete (see e.g. [ABG$^+$23, Corollary 14.2.5]), and we denote by $\text{colim}_{i \in \mathcal{I}} \mathcal{D}_i$ the *colimit* in $\omega \mathcal{C}at$ of a diagram $i \in \mathcal{I} \mapsto \mathcal{D}_i$.
- » Given an $\omega$-category $\mathcal{D}$, we denote by $\Sigma \mathcal{D}$ the *suspension* of $\mathcal{D}$, which is freely generated by two objects and one $(n+1)$-cell $\Sigma a$ between them for each $n$-cell $a$ of $\mathcal{D}$. A version of this construction is considered e.g. in [OR23, §2.2].
- » Given an $\omega$-category $\mathcal{D}$ and two objects $a$ and $b$, we denote by $\text{hom}_{\mathcal{D}}(a, b)$ the *hom-$\omega$-category* of $\mathcal{D}$ from $a$ to $b$, which has one $n$-cell for every $(n+1)$-cell $f$ of $\mathcal{D}$ for which $d_0^+ f = b$ and $d_0^- f = a$.

The existence of the following adjunction can be checked by direct inspection (cf. [AM20, §B.6.5]). The preservation of connected colimits can be deduced using a standard argument based on [Hir21, Proposition 2.9].

**Proposition 1.1.** *If $\omega \mathcal{C}at_{*,*}$ denotes the category of bipointed marked $\infty$-categories and bipointed $\omega$-functors, there is an adjunction*

$$\Sigma : \omega \mathcal{C}at \rightleftarrows \omega \mathcal{C}at_{*,*} : \text{hom}$$

*Moreover, the functor $\Sigma : \omega \mathcal{C}at \to \omega \mathcal{C}at$ preserves connected colimits.*

4

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

1.2. Equivalences and bi-equivalences in an $\omega$-category. The following is originally due to Métayer, and is also considered in [AL20, §1.2] (under the terminology of structure of reversibility) and [Lou23, Définition 1.1.7] (under the terminology of ensemble d'inversibilité).

Definition 1.2. Let $\mathcal{D}$ be an $\omega$-category. An invertibility set in $\mathcal{D}$ is a set $E = \coprod_{n>0} E_n$ with $E_n \subseteq \mathcal{D}_n$ such that, for all $n > 0$ and $a \in E_n$, there exists $\tilde{a} \in E_n$ of the form

$$\tilde{a} \colon d_{n-1}^+ a \to d_{n-1}^- a$$

and $c, c' \in E_{n+1}$ of the form

$$c \colon \tilde{a} \underset{n-1}{*} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a \underset{n-1}{*} \tilde{a} \to \mathrm{id}_{d_{n-1}^+ a}.$$

In the situation above we say that $\tilde{a}$ is a weak inverse for $a$.

Definition 1.3. Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \mathcal{D}_n$, the $n$-cell $a$ is said to be an $\omega$-equivalence if there exists an invertibility set $E$ such that $a \in E$. We denote by $\mathrm{eq}_n \mathcal{D}$ the set of all $n$-cells in $\mathcal{D}$ that are $\omega$-equivalences and by $\mathrm{eq} \mathcal{D} := \coprod_{n>0} \mathrm{eq}_n \mathcal{D}$ the set of all $\omega$-equivalences in $\mathcal{D}$.

The following is from [AL20, §1.2] and [Lou23, Lemme 1.1.8], and is generally taken as the defining property for the set $\mathrm{eq} \mathcal{D}$ of $\omega$-equivalences in an $\omega$-category $\mathcal{D}$ (see e.g. [LMW10, Definition 6]).

Proposition 1.4. Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \mathcal{D}_n$, we have that $a \in \mathrm{eq}_n \mathcal{D}$ if and only if there exist $\tilde{a} \in \mathcal{D}_n$ of the form

$$\tilde{a} \colon d_{n-1}^+ a \to d_{n-1}^- a$$

and $c, c' \in \mathrm{eq}_{n+1} \mathcal{D}$ of the form

$$c \colon \tilde{a} \underset{n-1}{*} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a \underset{n-1}{*} \tilde{a} \to \mathrm{id}_{d_{n-1}^+ a}.$$

Remark 1.5. Given an $\omega$-category $\mathcal{D}$, by Proposition 1.4 the set $\mathrm{eq} \mathcal{D}$ is the maximal invertibility set in $\mathcal{D}$.

Definition 1.6. Let $\mathcal{D}$ be an $\omega$-category. A bi-invertibility set in $\mathcal{D}$ is a set $E = \coprod_{n>0} E_n$ with $E_n \subseteq \mathcal{D}_n$ such that, for all $n > 0$ and $a \in E_n$, there exist $a^L, a^R \in \mathcal{D}_n$ of the form

$$a^L, a^R \colon d_{n-1}^+ a \to d_{n-1}^- a$$

and $c, c' \in E_{n+1}$ of the form

$$c \colon a^L \underset{n-1}{*} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a \underset{n-1}{*} a^R \to \mathrm{id}_{d_{n-1}^+ a}.$$

In the situation above, we say that $a^L$, resp. $a^R$, is a left inverse, resp. right inverse, for $a$.

Definition 1.7. Given an $\omega$-category $\mathcal{D}$ and $a \in \mathcal{D}_n$ with $n > 0$, the $n$-cell $a$ is said to be an $\omega$-bi-equivalence if there exists a bi-invertibility set $E$ such that $a \in E$. We denote by $\mathrm{bieq}_n \mathcal{D}$ the set of all $n$-cells in $\mathcal{D}$ that are $\omega$-bi-equivalences and by $\mathrm{bieq} \mathcal{D} := \coprod_{n>0} \mathrm{bieq}_n \mathcal{D}$ the set of all $\omega$-bi-equivalences in $\mathcal{D}$.

Remark 1.8. If $E$ is an invertibility set in an $\omega$-category $\mathcal{D}$, then $E$ is also a bi-invertibility set in $\mathcal{D}$.

The following is often taken as the defining property for the set $\mathrm{bieq} \mathcal{D}$ of $\omega$-bi-equivalences in an $\omega$-category $\mathcal{D}$ (cf. in [Ric20, Définition 4]).

A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

5

**Proposition 1.9.** *Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \mathcal{D}_n$, we have that $a \in \mathrm{bieq}_n \mathcal{D}$ if and only if there exist $a^L, a^R \in \mathcal{D}_n$ of the form*

$$a^L, a^R : d_{n-1}^+ a \rightarrow d_{n-1}^- a$$

*and $c, c' \in \mathrm{bieq}_{n+1} \mathcal{D}$ of the form*

$$c : a^L \begin{matrix} * \\ n-1 \end{matrix} a \rightarrow \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' : a \begin{matrix} * \\ n-1 \end{matrix} a^R \rightarrow \mathrm{id}_{d_{n-1}^+ a}.$$

*Proof.* For the forward direction, we suppose that $a \in \mathrm{bieq} \mathcal{D}$. By Definition 1.7 there exists a bi-invertibility set $E$ containing $a$, and by Definition 1.6 there exist $a^L, a^R \in \mathcal{D}_n$, and $c, c' \in E_{n+1}$ of the form displayed in Definition 1.6. Since $c, c' \in E$, by Definition 1.7 it follows that $c, c' \in \mathrm{bieq}_n \mathcal{D}$, as desired.

For the converse direction, suppose that for a given $a \in \mathcal{D}_n$ there exist $a^L, a^R \in \mathcal{D}_n$, $c, c' \in \mathrm{bieq}_{n+1} \mathcal{D}$ satisfying the conditions of the statement. By Definition 1.7 there exist bi-invertibility sets $E$ and $E'$ in $\mathcal{D}$ containing $c$ and $c'$, respectively. Then $E'' := \{a\} \cup E \cup E'$ is by Definition 1.6 an invertibility set containing $a$. By Definition 1.7, it follows that $a \in \mathrm{bieq}_n \mathcal{D}$, as desired. $\square$

We now establish some closure properties of the set of biequivalences in an $\omega$-category $\mathcal{D}$, which are essentially the content of [Ric20, Theorem 13].

**Lemma 1.10.** *Let $\mathcal{D}$ be an $\omega$-category. If we denote*

$$\mathrm{id}_n \mathcal{D} := \{\mathrm{id}_a \in \mathcal{D}_n \mid a \in \mathcal{D}_{n-k}, \ k > 0\},$$

*the set $\mathrm{id} \mathcal{D} := \coprod_{n>0} \mathrm{id} \mathcal{D}$ is a bi-invertibility set.*

*Proof.* This is straightforward from Definition 1.6. $\square$

**Proposition 1.11.** *Let $\mathcal{D}$ be an $\omega$-category and $n \geq 0$. Given $a \in \mathcal{D}_n$, we have that $\mathrm{id}_a \in \mathrm{bieq}_{n+1} \mathcal{D}$.*

*Proof.* A bi-invertibility set in the sense of Definition 1.6 containing $\mathrm{id}_a$ is constructed in Lemma 1.10. It follows from Definition 1.7 that $\mathrm{id}_a \in \mathrm{bieq}_{n+1} \mathcal{D}$, as desired. $\square$

**Lemma 1.12.** *Let $\mathcal{D}$ be an $\omega$-category. If we denote*

$$E_n := \{b *_k a \mid a, b \in \mathrm{bieq}_n \mathcal{D}, \ 0 \leq k < n-1\},$$

*the set $E := \coprod_{n>0} E_n$ is a bi-invertibility set.*

*Proof.* Given $e := b *_k a \in E_n$, by Proposition 1.9 there exist $a^L, a^R, b^L, b^R \in \mathcal{D}_n$, $c, c', d, d' \in \mathrm{bieq}_{n+1} \mathcal{D}$ of the form

$$c : a^L \begin{matrix} * \\ n-1 \end{matrix} a \rightarrow \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' : a \begin{matrix} * \\ n-1 \end{matrix} a^R \rightarrow \mathrm{id}_{d_{n-1}^+ a},$$

$$d : b^L \begin{matrix} * \\ n-1 \end{matrix} b \rightarrow \mathrm{id}_{d_{n-1}^- b} \quad \text{and} \quad d' : b \begin{matrix} * \\ n-1 \end{matrix} b^R \rightarrow \mathrm{id}_{d_{n-1}^+ b}.$$

We then define $e^R := b^R *_k a^R \in \mathcal{D}_n$ and $e^L := b^L *_k a^L \in \mathcal{D}_n$, and we set $\ell \in \mathcal{D}_{n+1}$ and $\ell' \in \mathcal{D}_{n+1}$ to be the composites

$$\ell := d \begin{matrix} * \\ k \end{matrix} c : e^L \begin{matrix} * \\ n-1 \end{matrix} e \rightarrow \mathrm{id}_{d_{n-1}^- e} \quad \text{and} \quad \ell' := d' \begin{matrix} * \\ k \end{matrix} c' : e \begin{matrix} * \\ n-1 \end{matrix} e^R \rightarrow \mathrm{id}_{d_{n-1}^+ e}.$$

These composites do make sense because various relations, such as an instance of the interchange law

$$e \begin{matrix} * \\ n-1 \end{matrix} e^R = (b *_k a) \begin{matrix} * \\ n-1 \end{matrix} (b^R *_k a^R) = (b \begin{matrix} * \\ n-1 \end{matrix} b^R) \begin{matrix} * \\ k \end{matrix} (a \begin{matrix} * \\ n-1 \end{matrix} a^R)$$

6

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

hold. By definition we see that $\ell \in E_{n+1}$ and $\ell' \in E_{n+1}$, so it follows that $E$ is a bi-invertibility set containing $e$, as desired. $\square$

**Proposition 1.13.** *Let $\mathcal{D}$ be an $\omega$-category and $0 \leq k < n-1$. Given $a, b \in \mathrm{bieq}_n \mathcal{D}$ such that $b *_k a$ is defined, we have that $b *_k a \in \mathrm{bieq}_n \mathcal{D}$.*

*Proof.* A bi-invertibility set in the sense of Definition 1.6 containing $b *_k a$ is constructed in Lemma 1.12. It follows from Definition 1.7 that $b *_k a \in \mathrm{bieq}_n \mathcal{D}$, as desired. $\square$

**Lemma 1.14.** *Let $\mathcal{D}$ be an $\omega$-category. If we denote*

$$E_n := \{b_{n-1} * a \in \mathcal{D}_n \mid a, b \in \mathrm{bieq}_n \mathcal{D}\},$$

*the set $E := \coprod_{n>0} E_n$ is a bi-invertibility set.*

*Proof.* Given $e := b *_{n-1} a \in E_n$, by Proposition 1.9 there exist $a^L, a^R, b^L, b^R \in \mathcal{D}_n$ and $c, c', d, d' \in \mathrm{bieq}_{n+1} \mathcal{D}$ of the form

$$c \colon a^L *_{n-1} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a *_{n-1} a^R \to \mathrm{id}_{d_{n-1}^+ a};$$

$$d \colon b^L *_{n-1} b \to \mathrm{id}_{d_{n-1}^- b} \quad \text{and} \quad d' \colon b *_{n-1} b^R \to \mathrm{id}_{d_{n-1}^+ b}.$$

We then define $e^L := a^L *_{n-1} b^L \in \mathcal{D}_n$ and $e^R := a^R *_{n-1} b^R \in \mathcal{D}_n$, and set $\ell \in \mathcal{D}_{n+1}$ and $\ell' \in \mathcal{D}_{n+1}$ to be the composites

$$\ell := c *_{n} (\mathrm{id}_{a^L *_{n-1}} d *_{n-1} \mathrm{id}_a) \colon e^L *_{n-1} e \to \mathrm{id}_{d_{n-1}^- e}$$

$$\ell' := d' *_{n} (\mathrm{id}_b *_{n-1} c' *_{n-1} \mathrm{id}_{b^R}) \colon e *_{n-1} e^R \to \mathrm{id}_{d_{n-1}^+ e}.$$

These composites do make sense because composition is associative and various relations, such as $d_{n-1}^- a = d_{n-1}^- e$, hold. By Propositions 1.11 and 1.13 we can recognize that $\ell$ and $\ell'$ are composites of $\omega$-bi-equivalences of dimension $n+1$ along cells of dimension $n$, so by definition of $E$ we obtain that $\ell, \ell' \in E_{n+1}$. So $E$ is a bi-invertibility set containing $e$, as desired. $\square$

**Proposition 1.15.** *Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a, b \in \mathrm{bieq}_n \mathcal{D}$ such that $b *_{n-1} a \in \mathcal{D}_n$, we have that $b *_{n-1} a \in \mathrm{bieq}_n \mathcal{D}$.*

*Proof.* A bi-invertibility set in the sense of Definition 1.6 containing $b *_{n-1} a$ is constructed in Lemma 1.14. It follows from Definition 1.7 that $b *_{n-1} a \in \mathrm{bieq}_n \mathcal{D}$, as desired. $\square$

**Lemma 1.16.** *Let $\mathcal{D}$ be an $\omega$-category. If we denote*

$$E_n := \{b *_{n-1} a^L \in \mathcal{D}_n \mid a, b \in \mathrm{bieq}_n \mathcal{D}, a^L \text{ is a left inverse for } a\},$$

*then the set $E := \coprod_{n>0} E_n$ is a bi-invertibility set.*

*Proof.* Given $e := b *_{n-1} a^L \in E_n$ for $a, b \in \mathrm{bieq}_n \mathcal{D}$, by Proposition 1.9 there exist $a^R, b^L, b^R \in \mathcal{D}_n$ and $c, c', d, d' \in \mathrm{bieq}_{n+1} \mathcal{D}$ of the form

$$c \colon a^L *_{n-1} a \to \mathrm{id}_{d_{n-1}^- a} \quad \text{and} \quad c' \colon a *_{n-1} a^R \to \mathrm{id}_{d_{n-1}^+ a},$$

$$d \colon b^L *_{n-1} b \to \mathrm{id}_{d_{n-1}^- b} \quad \text{and} \quad d' \colon b *_{n-1} b^R \to \mathrm{id}_{d_{n-1}^+ b}.$$

A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

7

We first consider $x, y \in \mathcal{D}_{n+1}$ defined as follows:

$$\begin{aligned} y: & a \begin{array}{cc} * & b^L \\ n-1 & n-1 \end{array} & b \begin{array}{cc} * & a^L \\ n-1 & n-1 \end{array} & a \begin{array}{cc} * & a^R \\ n-1 & n-1 \end{array} \xrightarrow{\text{id}_a \begin{array}{cc} * & c \\ n-1 & n-1 \end{array} \begin{array}{cc} * & \text{id}_a R \end{array}} & a \begin{array}{cc} * & a^R \\ n-1 & n-1 \end{array} \xrightarrow{c'} & \text{id}_{d_{n-1}^+} a \\ x: & a \begin{array}{cc} * & b^L \\ n-1 & n-1 \end{array} & b \begin{array}{cc} * & a^L \\ n-1 & n-1 \end{array} & a \begin{array}{cc} * & a^R \\ n-1 & n-1 \end{array} \xrightarrow{\text{id}_a \begin{array}{cc} * & b^L \\ n-1 & n-1 \end{array} \begin{array}{cc} * & a^L \\ n-1 & n-1 \end{array} \begin{array}{cc} * & c' \\ n-1 & n-1 \end{array}} & a \begin{array}{cc} * & b^L \\ n-1 & n-1 \end{array} \begin{array}{cc} * & a^L \\ n-1 & n-1 \end{array} \end{aligned}$$

By Propositions 1.11, 1.13 and 1.15, we know that $x, y \in \text{bieq}_{n+1} \mathcal{D}$. If $x^L$ denotes a left inverse for $x$, we then define $e^L := a \begin{array}{cc} * & n-1 \\ n-1 & b^L \end{array} \in \mathcal{D}_n$ and $e^R := a \begin{array}{cc} * & n-1 \\ n-1 & b^R \end{array} \in \mathcal{D}_n$, and set $\ell \in \mathcal{D}_{n+1}$ and $\ell' \in \mathcal{D}_{n+1}$ to be the composites

$$\begin{aligned} \ell: & e^L \begin{array}{cc} * & e \\ n-1 & \end{array} \xrightarrow{x^L} & a \begin{array}{cc} * & b^L \\ n-1 & \end{array} & b \begin{array}{cc} * & a^L \\ n-1 & \end{array} & a \begin{array}{cc} * & a \\ n-1 & \end{array} \xrightarrow{x} & a^R \xrightarrow{y} & \text{id}_{d_{n-1}^-} e \\ \ell': & e \begin{array}{cc} * & e \\ n-1 & \end{array} \xrightarrow{\text{id}_a \begin{array}{cc} * & c \\ n-1 & n-1 \end{array} \begin{array}{cc} * & \text{id}_a R \end{array}} & b \begin{array}{cc} * & d' \\ n-1 & \end{array} \xrightarrow{d'} & \text{id}_{d_{n-1}^+} e \end{aligned}$$

By construction, we see that $\ell \in E_{n+1}$. By Propositions 1.11, 1.13 and 1.15, we see that $\ell' \in \text{bieq}_{n+1} \mathcal{D}$, and in particular $\ell' = \ell' \begin{array}{cc} * & \text{id}_{d_n^- \ell'} \end{array} \in E_{n+1}$, so we get that $E$ is a bi-invertibility set containing $e$, as desired. $\square$

**Proposition 1.17** ([Ric20, Lemma 14]). *Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \text{bieq}_n \mathcal{D}$, if $a^L$ and $a^R$ are, respectively, a left and right weak inverse for $a$, then $a^L, a^R \in \text{bieq}_n \mathcal{D}$.*

*Proof.* A bi-invertibility set in the sense of Definition 1.6 containing $a^L$ is constructed in Lemma 1.16, and one for $a^R$ can be constructed with a similar argument. It follows from Definition 1.7 that $a^L, a^R \in \text{bieq}_n \mathcal{D}$, as desired. $\square$

**Lemma 1.18.** *Given an $\omega$-category $\mathcal{D}$, we have that $\text{bieq} \mathcal{D} := \coprod_{n>0} \text{bieq}_n \mathcal{D}$ is an invertibility set.*

*Proof.* Given $a \in \text{bieq}_n \mathcal{D}$, by Definition 1.6 there exist $a^L, a^R \in \mathcal{D}_n$ and $c, c' \in \text{bieq}_{n+1} \mathcal{D}$ of the form

$$c: & a^L \begin{array}{cc} * & a \\ n-1 & \end{array} \to \text{id}_{d_{n-1}^-} a \quad \text{and} \quad c': & a \begin{array}{cc} * & a \\ n-1 & \end{array} \xrightarrow{x} & a^R \to \text{id}_{d_{n-1}^+} a.$$

If $c'^L \in \mathcal{D}_{n+1}$ is a left inverse for $c'$, we set $\ell \in \mathcal{D}_{n+1}$ to be the composite

$$\ell: & a \begin{array}{cc} * & a^L \\ n-1 & \end{array} \xrightarrow{\text{id}_a \begin{array}{cc} * & a^L \\ n-1 & \end{array} \begin{array}{cc} * & c \\ n-1 & \end{array}} & a \begin{array}{cc} * & a^L \\ n-1 & \end{array} \xrightarrow{x} & a^R \xrightarrow{\text{id}_a \begin{array}{cc} * & c \\ n-1 & n-1 \end{array} \begin{array}{cc} * & \text{id}_a R \end{array}} & a \begin{array}{cc} * & c' \\ n-1 & \end{array} \xrightarrow{d} & a^R \xrightarrow{c'} & \text{id}_{d_{n-1}^+} a.$$

By Proposition 1.17 we know that $a^L \in \text{bieq}_n \mathcal{D}$, and by Propositions 1.11, 1.13, 1.15 and 1.17 we know that $\ell \in \text{bieq}_{n+1} \mathcal{D}$. Given that we also have that $c \in \text{bieq}_{n+1} \mathcal{D}$, this shows that $\text{bieq} \mathcal{D}$ is an invertibility set, as desired. $\square$

**Proposition 1.19** ([Ric20, Corollary 19]). *Let $\mathcal{D}$ be an $\omega$-category and $n > 0$. Given $a \in \mathcal{D}_n$, we have that $a \in \text{eq}_n \mathcal{D}$ if and only if $a \in \text{bieq}_n \mathcal{D}$.*

*Proof.* If $a \in \text{eq}_n \mathcal{D}$ (resp. $a \in \text{bieq}_n \mathcal{D}$), a bi-invertibility set (resp. invertibility set) containing $a$ is constructed in Remarks 1.5 and 1.8 (resp. Lemma 1.18). It follows from Definition 1.7 (resp. Definition 1.3) that $a \in \text{bieq}_n \mathcal{D}$ (resp. $a \in \text{eq}_n \mathcal{D}$), as desired. $\square$

8

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

### 1.3. The homotopy theory of $\omega$-categories.

**Theorem 1.20** ([LMW10, §4,5]). *There exists a model structure on the category $\omega Cat$ of $\omega$-categories, which we denote $\omega Cat_{\text{can}}$ and call the canonical model structure, in which:*

- *every object is fibrant.*
- *the class of cofibrations is generated by the set of boundary inclusions $\partial \mathcal{C}_n \hookrightarrow \mathcal{C}_n$ for $n \geq 0$.*
- *the cofibrant objects are precisely the polygraphs, considered e.g. in [LMW10, §5].*

*Proof.* The model structure $\omega Cat_{\text{can}}$ is constructed in [LMW10, Theorem 4.39], and the description of the fibrant and cofibrant objects can be found in [LMW10, §5].

### 1.4. The model for the coherent $\omega$-equivalence.

**Construction 1.21.** We denote by $\mathcal{Q}$ the free category generated by three 1-cells $f: p \to q$, $g: q \to p$ and $g': q \to p$. This is obtained by gluing $f$ "head-to-tail" with both $g$ and $g'$, and generating all possible compositions. The set of objects is $\text{Ob } \mathcal{Q} = \{p, q\}$. The category $\mathcal{Q}$ as a whole can be understood as the pushout in $\omega Cat$

$$\begin{array}{c} \partial \mathcal{C}_1^\circ \amalg \partial \mathcal{C}_1 \amalg \partial \mathcal{C}_1^\circ \xrightarrow{\quad} \mathcal{C}_0 \amalg \mathcal{C}_0 \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \mathcal{C}_1^\circ \amalg \mathcal{C}_1 \amalg \mathcal{C}_1^\circ \xrightarrow{\quad} \mathcal{Q} \end{array}$$

**Construction 1.22.** Let $\widehat{\omega \mathcal{E}}^{(0)} := \mathcal{C}_0 \amalg \mathcal{C}_0$. For $k > 0$, we define inductively $\widehat{\omega \mathcal{E}}^{(k)}$ to be an $\omega$-category (in fact a $k$-category) coming with a triple of $\omega$-functors

$$\iota_k: \widehat{\omega \mathcal{E}}^{(k-1)} \to \widehat{\omega \mathcal{E}}^{(k)} \quad \text{and} \quad \alpha_k, \beta_k: \Sigma(\widehat{\omega \mathcal{E}}^{(k-1)}) \to \widehat{\omega \mathcal{E}}^{(k)}.$$

- For $k = 1$, we let $\widehat{\omega \mathcal{E}}^{(1)} := \mathcal{Q}$, we let $\iota_1$ be the inclusion

$$\widehat{\omega \mathcal{E}}^{(0)} = \mathcal{C}_0 \amalg \mathcal{C}_0 \hookrightarrow \mathcal{Q} = \widehat{\omega \mathcal{E}}^{(1)}$$

and we let $\alpha_1$ and $\beta_1$

$$\alpha_1: \Sigma \widehat{\omega \mathcal{E}}^{(0)} = \mathcal{C}_1 \amalg \mathcal{C}_1 \to \mathcal{Q} = \widehat{\omega \mathcal{E}}^{(1)} \quad \text{and} \quad \beta_1: \Sigma \widehat{\omega \mathcal{E}}^{(0)} = \mathcal{C}_1 \amalg \mathcal{C}_1 \to \mathcal{Q} = \widehat{\omega \mathcal{E}}^{(1)}$$

be the $\omega$-functors determined by

$$\alpha_1: \Sigma p \mapsto g \begin{smallmatrix} * & f, & \Sigma q \mapsto \text{id}_p, \\ 0 & * & \text{and} \\ 0 & \beta_1: \Sigma p \mapsto f \begin{smallmatrix} * & g', & \Sigma q \mapsto \text{id}_q. \end{smallmatrix} \end{smallmatrix}$$

- For $k > 1$, we let $\widehat{\omega \mathcal{E}}^{(k)}$, $\iota_k$, $\alpha_k$, and $\beta_k$ be defined by the pushout in $\omega Cat$

$$\begin{array}{c} \Sigma(\widehat{\omega \mathcal{E}}^{(k-2)}) \amalg \Sigma(\widehat{\omega \mathcal{E}}^{(k-2)}) \xrightarrow{[\alpha_{k-1}, \beta_{k-1}]} \widehat{\omega \mathcal{E}}^{(k-1)} \\ \Sigma(\iota_{k-1}) \amalg \Sigma(\iota_{k-1}) \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \iota_k \\ \Sigma(\widehat{\omega \mathcal{E}}^{(k-1)}) \amalg \Sigma(\widehat{\omega \mathcal{E}}^{(k-1)}) \xrightarrow{[\alpha_k, \beta_k]} \widehat{\omega \mathcal{E}}^{(k)}. \end{array} \tag{1.23}$$

**Construction 1.24.** We denote by $\widehat{\omega \mathcal{E}}$ the $\omega$-category obtained as the colimit in $\omega Cat$

$$\widehat{\omega \mathcal{E}} := \text{colim}[ \quad \cdots \leftarrow \widehat{\omega \mathcal{E}}^{(k+1)} \xleftarrow{\iota_{k+1}} \widehat{\omega \mathcal{E}}^{(k)} \leftarrow \cdots \leftarrow \widehat{\omega \mathcal{E}}^{(2)} \xleftarrow{\iota_2} \widehat{\omega \mathcal{E}}^{(1)} \xleftarrow{\iota_1} \widehat{\omega \mathcal{E}}^{(0)} \quad ].$$

A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

9

Remark 1.25. The $\omega$-functors $\alpha_k, \beta_k \colon \Sigma(\widehat{\omega\mathcal{E}}^{(k-1)}) \to \widehat{\omega\mathcal{E}}^{(k)}$ induce $\omega$-functors

$$\alpha_\infty, \beta_\infty \colon \Sigma(\widehat{\omega\mathcal{E}}) \to \widehat{\omega\mathcal{E}}.$$

The following result justifies the name of walking $\omega$-equivalence.

Proposition 1.26. Let $\mathcal{D}$ be an $\omega$-category. Given $a \in \mathcal{D}_n$, we have that $a \in \mathrm{bieq}_n\mathcal{D}$ if and only if there exists an $\omega$-functor $\tilde{a} \colon \Sigma^{n-1}(\widehat{\omega\mathcal{E}}) \to \mathcal{D}$ such that the following diagram commutes:

$$\begin{array}{c} \mathcal{C}_n \xrightarrow{\quad a \quad} \mathcal{D} \\ \Sigma^{n-1}f \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \Sigma^{n-1}(\widehat{\omega\mathcal{E}}) \end{array} \tag{1.27}$$

Proof. For each $n \ge 0$ and $a \in \mathrm{bieq}_n\mathcal{D}$, make a choice of $a^L, a^R \in \mathcal{D}_n$ and of $c_a, c'_a \in \mathrm{bieq}_{n+1}\mathcal{D}$ of the form

$$c_a \colon a^L \underset{n-1}{*} a \to \mathrm{id}_{d_{n-1}^-a} \quad \text{and} \quad c'_a \colon a \underset{n-1}{*} a^R \to \mathrm{id}_{d_{n-1}^+a}.$$

By recursion on $k \ge 0$, we construct families of $\omega$-functors

$$\tilde{a}^{(k)} \colon \Sigma^{n-1}\widehat{\omega\mathcal{E}}^{(k)} \to \mathcal{D}$$

parameterized by $n \ge 0$ and $a \in \mathrm{bieq}_n\mathcal{D}$, such that

$$\begin{array}{c} \mathcal{C}_n \xrightarrow{\quad a \quad} \mathcal{D} \\ \Sigma^{n-1}f \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \\ \Sigma^{n-1}(\widehat{\omega\mathcal{E}}^{(k)}) \end{array}$$

commutes, and satisfying

$$(1.28) \ \tilde{a}^{(k-1)} = \tilde{a}^{(k)} \circ \Sigma^{n-1}(\iota_k) \text{ and } [\tilde{c}_a^{(k-1)}, \tilde{c}'_a^{(k-1)}] = \tilde{a}^{(k)} \circ [\Sigma^{n-1}(\alpha_k), \Sigma^{n-1}(\beta_k)]$$

for all $k > 0$. For each $n \in \mathbb{N}$ and $a \in \mathrm{bieq}_n\mathcal{D}$, we let $\tilde{a}^{(1)}$ be defined by

$$\Sigma^{n-1}f \mapsto a, \quad \Sigma^{n-1}g \mapsto a^L, \quad \Sigma^{n-1}g' \mapsto a^R,$$

and set $\tilde{a}^{(0)} := \tilde{a}^{(1)} \circ \Sigma^{n-1}(\iota_1)$. Then the equality

$$[\tilde{c}_a^{(0)}, \tilde{c}'_a^{(0)}] = \tilde{a}^{(1)} \circ [\Sigma^{n-1}(\alpha_1), \Sigma^{n-1}(\beta_1)]$$

holds by construction.

Let $k > 1$, $n \in \mathbb{N}$, and $a \in \mathrm{bieq}_n\mathcal{D}$. By the inductive hypothesis, we have a commutative diagram in $\omega\mathcal{C}at$

$$\begin{array}{c} \Sigma^n(\widehat{\omega\mathcal{E}}^{(k-2)}) \amalg \Sigma^n(\widehat{\omega\mathcal{E}}^{(k-2)}) \xrightarrow{[\Sigma^{n-1}(\alpha_{k-1}), \Sigma^{n-1}(\beta_{k-1})]} \Sigma^{n-1}(\widehat{\omega\mathcal{E}}^{(k-1)}) \\ \downarrow \Sigma^n(\iota_{k-1}) \amalg \Sigma^n(\iota_{k-1}) \\ \Sigma^n(\widehat{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma^n(\widehat{\omega\mathcal{E}}^{(k-1)}) \xrightarrow{[\tilde{c}_a^{(k-1)}, \tilde{c}'_a^{(k-1)}]} \mathcal{D}. \end{array}$$

Using the universal property of the pushout (1.23) and the fact that $\Sigma^{n-1}$ preserves pushouts by Proposition 1.1, we see that this diagram induces a unique $\omega$-functor

$$\tilde{a}^{(k)} \colon \Sigma^{n-1}\widehat{\omega\mathcal{E}}^{(k)} \to \mathcal{D}$$

10

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

satisfying (1.28). This completes the inductive step. Since $\Sigma^{n-1}$ preserves sequential colimits by Proposition 1.1, for each $a \in \mathrm{bieq}_n\mathcal{D}$, we obtain universally an $\omega$-functor $\tilde{a} \colon \Sigma^{n-1}(\widehat{\omega\mathcal{E}}) \to \mathcal{D}$ such that (1.27) commutes.

Conversely, for each $n \geq 0$, let

$$E_n := \{a \in \mathcal{D}_n \mid \text{there exists } \tilde{a} \colon \Sigma^{n-1}\widehat{\omega\mathcal{E}} \to \mathcal{D} \text{ such that } a = \tilde{a} \circ \Sigma^{n-1}f\};$$

we will show that $E := \coprod_{n \geq 0} E_n$ is a bi-invertibility set. Let $a \in E_n$. By definition there exists $\tilde{a}$ such that $a = \tilde{a} \circ \Sigma^{n-1}f$. In particular, there are $(n+1)$-cells

$$c \colon a^L \begin{matrix} * & a \to \mathrm{id}_{d_{n-1}^-a} \end{matrix} \quad \text{and} \quad c' \colon a \begin{matrix} * & a^R \to \mathrm{id}_{d_{n-1}^+a} \end{matrix}$$

in the image of $\Sigma^{n-1}\widehat{\omega\mathcal{E}}^{(2)}$ through $\tilde{a}$. Then

$$\tilde{c} := \tilde{a} \circ \Sigma^{n-1}(\alpha_\infty) \colon \Sigma^n\widehat{\omega\mathcal{E}} \to \mathcal{D} \quad \text{and} \quad \tilde{c}' := \tilde{a} \circ \Sigma^{n-1}(\beta_\infty) \colon \Sigma^n\widehat{\omega\mathcal{E}} \to \mathcal{D}$$

are $\omega$-functors satisfying

$$c = \tilde{c} \circ \Sigma^n f, \qquad c' = \tilde{c}' \circ \Sigma^n f.$$

It follows that $c, c' \in E_{n+1}$. This completes the proof.

*Remark 1.29.* By construction, $\widehat{\omega\mathcal{E}}$ is a polygraph, whose set of $k$-cells is freely generated by the set $E_k$ defined, inductively on $k$, by

$$(1.30) \quad E_0 := \{p, q\}, \; E_1 := \{f, g, g'\}, \; E_k := \alpha_\infty(\Sigma E_{k-1}) \cup \beta_\infty(\Sigma E_{k-1}) \text{ for } k > 1.$$

**Lemma 1.31.** *With reference to the notation of (1.30), let $n > 0$ and $a \in E_n$. Then $a \in \mathrm{bieq}_n\widehat{\omega\mathcal{E}}$.*

*Proof.* First, suppose that $n = 1$ and $a = f$. Then the classifying $\omega$-functor $f \colon \mathcal{C}_1 \to \widehat{\omega\mathcal{E}}$ factors as $\mathrm{id}_{\widehat{\omega\mathcal{E}}} \circ f$ as in

![img-0.jpeg](img-0.jpeg)

So, by Proposition 1.26 $f \in \mathrm{bieq}_1\widehat{\omega\mathcal{E}}$. If $a = g$ or $a = g'$, then $a$ is a left or right weak inverse of $f$, so by Proposition 1.17, the 1-morphism $a$ is also a biequivalence.

Now, suppose that $n > 1$. Then there exists $e \in E_{n-1}$ such that $a = \alpha_\infty(\Sigma e)$ or $a = \beta_\infty(\Sigma e)$, and by the inductive hypothesis $e \in \mathrm{bieq}_{n-1}\widehat{\omega\mathcal{E}}$. By Proposition 1.26, there exists $\tilde{e} \colon \Sigma^{n-2}\widehat{\omega\mathcal{E}} \to \widehat{\omega\mathcal{E}}$ such that $e$ factors as in

![img-1.jpeg](img-1.jpeg)

Assume without loss of generality that $a = \alpha_\infty(\Sigma e)$. Then, letting $\tilde{a} := \alpha_\infty \circ \Sigma\tilde{e}$, we have that

$$a = \alpha_\infty \circ \Sigma(\tilde{e} \circ \Sigma^{n-2}f) = (\alpha_\infty \circ \Sigma\tilde{e}) \circ \Sigma(\Sigma^{n-2}f) = \tilde{a} \circ \Sigma^{n-1}f.$$

A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

11

so $a$ factors as in

![img-2.jpeg](img-2.jpeg)

Hence, we conclude by Proposition 1.26 that $a \in \mathrm{bieq}_n \widehat{\omega\mathcal{E}}$, as desired. $\square$

**Proposition 1.32.** *Let $n > 0$ and $a \in (\widehat{\omega\mathcal{E}})_n$. Then $a \in \mathrm{bieq}_n \widehat{\omega\mathcal{E}}$.*

*Proof.* By Remark 1.29, the cells of $\widehat{\omega\mathcal{E}}$ are composition-generated, in the sense of [ABG$^+$23, Proposition 15.1.8], by the cells in $E := \coprod_{k \geq 0} E_k$. By Lemma 1.31, all the generators are biequivalences, and by Proposition 1.15 and Proposition 1.13, biequivalences are closed under composition. $\square$

The remainder of the paper is devoted to proving the following.

**Theorem 1.33.** *The unique $\omega$-functor $\widehat{\omega\mathcal{E}} \to \mathcal{C}_0$ is a weak equivalence in $\omega\mathcal{C}at_{\mathrm{can}}$.*

## 2. THE MARKED MODEL FOR THE COHERENT $\omega$-EQUIVALENCE

**2.1. Marked $\omega$-categories.** We briefly recall some notions on marked $\omega$-categories from [HL23, §2] that will be needed in this paper.

A *marked $\omega$-category* is a pair $(\mathcal{D}, t\mathcal{D})$ where $\mathcal{D}$ is an $\omega$-category and $t\mathcal{D} := \coprod_{n \geq 0} t\mathcal{D}_n$ is a sequence of sets such that for any $n > 0$, the set $t\mathcal{D}_n$ is a subset of $\mathcal{D}_n$ containing identities and closed under composition. The $\omega$-category $\mathcal{D}$ is called *the underlying $\omega$-category* and $t\mathcal{D}$ *the marking* of $\mathcal{D}$. A cell in $t\mathcal{D}$ is called *marked*. A *marked $\omega$-functor* $F: (\mathcal{D}, t\mathcal{D}) \to (\mathcal{E}, t\mathcal{E})$ consists of a marking-preserving $\omega$-functor $F: \mathcal{D} \to \mathcal{E}$. We denote $\omega\mathcal{C}at^+$ the category of marked $\omega$-categories and marked $\omega$-functors. The assignment $(\mathcal{D}, t\mathcal{D}) \mapsto \mathcal{D}$ of the underlying $\omega$-category of any marked $\omega$-category defines a forgetful functor $U: \omega\mathcal{C}at^+ \to \omega\mathcal{C}at$.

**Notation 2.1.** Given an $\omega$-category $\mathcal{D}$, one can consider various choices of interest for the marking on $\mathcal{D}$:

- » If $\mathrm{id}\,\mathcal{D}$ denotes the set of identities of $\mathcal{D}$, the class $\mathrm{id}\,\mathcal{D}$ is closed under composition and contains identities. So, $(\mathcal{D}, \mathrm{id}\,\mathcal{D}) =: \mathcal{D}^\flat$ is a marked $\omega$-category. The assignment $\mathcal{D} \mapsto \mathcal{D}^\flat$ defines a functor $(-)^\flat: \omega\mathcal{C}at \to \omega\mathcal{C}at^+$.
- » If $\mathrm{mor}\,\mathcal{D}$ denotes the set of cells of $\mathcal{D}$ of strictly positive dimension, the class $\mathrm{mor}\,\mathcal{D}$ is closed under composition and contains identities. So, $(\mathcal{D}, \mathrm{mor}\,\mathcal{D}) =: \mathcal{D}^\sharp$ is a marked $\omega$-category. The assignment $\mathcal{D} \mapsto \mathcal{D}^\sharp$ defines a functor $(-)^\sharp: \omega\mathcal{C}at \to \omega\mathcal{C}at^+$.
- » If $\mathrm{eq}\,\mathcal{D}$ denotes the set of $\omega$-equivalences of $\mathcal{D}$ as in Definition 1.3, by [ABG$^+$23, Lemma 20.1.4] the class $\mathrm{eq}\,\mathcal{D}$ is closed under composition and contains identities. So, $(\mathcal{D}, \mathrm{eq}\,\mathcal{D}) =: \mathcal{D}^\sharp$ is a marked $\omega$-category. By Proposition 1.26, the assignment $\mathcal{D} \mapsto \mathcal{D}^\sharp$ defines a functor $(-)^\sharp: \omega\mathcal{C}at \to \omega\mathcal{C}at^+$.

The following adjoint pairs can be checked by verifying the appropriate universal properties, and using Proposition 1.1 for the second one.

**Proposition 2.2.** *There are adjunctions*

$$(-)^\flat: \omega\mathcal{C}at \rightleftarrows \omega\mathcal{C}at^+: U \quad \text{and} \quad U: \omega\mathcal{C}at^+ \rightleftarrows \omega\mathcal{C}at: (-)^\sharp.$$

*In particular, the functor $U: \omega\mathcal{C}at^+ \to \omega\mathcal{C}at$ preserves limits and colimits.*

12

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

**Proposition 2.3.** If $\omega Cat_{*,*}^{+}$ denotes the category of bipointed marked $\infty$-categories, there is an adjunction

$$\Sigma: \omega Cat^{+} \rightleftarrows \omega Cat_{*,*}^{+}: \mathrm{hom}$$

Moreover, the functor $\Sigma: \omega Cat^{+} \to \omega Cat^{+}$ preserves connected colimits.

**2.2. The coinductive homotopy theory of marked $\omega$-categories.** We recall that a left semi-model category structure on a category $\mathcal{M}$ consists of three distinguished classes of morphisms of $\mathcal{M}$, called *cofibrations*, *fibrations*, and *weak equivalences*, satisfying a weaker version of the axioms for a model category. We refer the reader to [BW24, Definition 2.1] for a complete list of axioms that these classes must satisfy. An object in $\mathcal{M}$ is said to be *fibrant* if the unique morphism to the terminal object of $\mathcal{M}$ is a fibration, and it is said to be *cofibrant* if the unique morphism from the initial object of $\mathcal{M}$ is a cofibration. The class of *acyclic cofibrations* is the class of morphisms in $\mathcal{M}$ that have the left lifting property with respect to all fibrations between fibrant objects. In a left semi-model structure, the class of acyclic cofibrations is closed under transfinite composition and pushouts and the class of weak equivalences is closed under two-out-of-three.

**Theorem 2.4** ([HL23, §4.2]). There exists a left semi-model structure on $\omega Cat^{+}$, which we denote by $\omega Cat_{\mathrm{coind}}^{+}$ and we call the coinductive left semi-model structure, such that:

(1) a marked $\omega$-functor $f: (\mathcal{D}, t\mathcal{D}) \to (\mathcal{E}, t\mathcal{E})$ is a cofibration in $\omega Cat_{\mathrm{coind}}^{+}$ if and only if the $\omega$-functor $f: \mathcal{D} \to \mathcal{E}$ is a cofibration in $\omega Cat_{\mathrm{can}}$;
(2) a cofibration $f: (\mathcal{D}, t\mathcal{D}) \to (\mathcal{E}, t\mathcal{E})$ between cofibrant objects is a weak equivalence in $\omega Cat_{\mathrm{coind}}^{+}$ if and only if it is an acyclic cofibration, that is, it has the left lifting property against fibrations between fibrants objects;
(3) a marked $\omega$-category $(\mathcal{D}, t\mathcal{D})$ is fibrant in $\omega Cat_{\mathrm{coind}}^{+}$ if and only if $t\mathcal{D} = \mathrm{eq}\,\mathcal{D}$;
(4) a marked $\omega$-functor $f: \mathcal{D}^{\natural} \to \mathcal{E}^{\natural}$ between fibrant objects is a weak equivalence in $\omega Cat_{\mathrm{coind}}^{+}$ if and only the $\omega$-functor $f: \mathcal{D} \to \mathcal{E}$ is a weak equivalence in $\omega Cat_{\mathrm{can}}$;
(5) a marked $\omega$-functor $f: \mathcal{D}^{\natural} \to \mathcal{E}^{\natural}$ between fibrant objects is a fibration in $\omega Cat_{\mathrm{coind}}^{+}$ if and only if it has the right lifting property against the marked $\infty$-functors of the form $i_{n}^{+}: \mathcal{C}_{n}^{\flat} \to (\mathcal{C}_{n+1}, \{e_{n+1}\} \cup \mathrm{id}(\mathcal{C}_{n+1}))$ for all $n \geq 0$. Here, $e_{n+1}$ denotes the non-trivial $(n+1)$-cell of $\mathcal{C}_{n+1}$ and $i_{n}^{+}$ denotes the marked $\omega$-functor that embeds $\mathcal{C}_{n}$ as the codomain of $e_{n+1}$.

*Proof.* The left semi-model structure $\omega Cat_{\mathrm{coind}}^{+}$ is built in [HL23, Definition 4.22] as a left Bousfield localization (in the sense of [BW24, Theorem A]) of the *saturated inductive left semi-model structure* from [HL23, Theorem 3.31]. The saturated inductive left semi-model structure is in turn built as a left Bousfield localization of the *inductive left semi-model structure* from [HL23, Theorem 2.38].

The characterization (1) of cofibrations directly follows from [HL23, Definition 2.27]. The characterization (2) of cofibrations between cofibrant objects that are weak equivalences follows from [Hen20, Proposition 2.2.10]. The characterization (3) of fibrant objects and the characterization (4) of weak equivalences between fibrant objects are in [HL23, Theorem 4.25]. The characterization (5) of fibrations between fibrant objects then directly follows from [HL23, Proposition 3.23], evoking [Hen23, Theorem 7.3(6)] for the fact that a map between fibrant objects in the left Bousfield localization $\omega Cat_{\mathrm{coind}}$ is a fibration if and only if it is one in the inductive left semi-model structure. $\square$

A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

13

**Lemma 2.5.** Given a marked $\omega$-category $(\mathcal{E}, t\mathcal{E})$ with $t\mathcal{E} \subseteq \operatorname{eq}\mathcal{E}$, the canonical morphism

$$(\mathcal{E}, t\mathcal{E}) \hookrightarrow \mathcal{E}^{\natural}$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^{+}$.

Proof. In order to show that $(\mathcal{E}, t\mathcal{E}) \to \mathcal{E}^{\natural}$ has the left lifting property with respect to any fibration between fibrant objects $p: \mathcal{B}^{\natural} \to \mathcal{D}^{\natural}$ in $\omega\mathcal{C}at_{\text{coind}}^{+}$, consider the following lifting problem in $\omega\mathcal{C}at^{+}$:

![img-3.jpeg](img-3.jpeg)

A lift exists (because $(-)^{\natural}: \omega\mathcal{C}at \to \omega\mathcal{C}at^{+}$ is a functor), and is necessarily given by the top map at the level of underlying categories. It follows that $(\mathcal{E}, t\mathcal{E}) \to \mathcal{E}^{\natural}$ is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^{+}$, as desired. $\square$

**Notation 2.6.** Given a marked $\infty$-category $(\mathcal{D}, t\mathcal{D})$, we denote by $\Sigma(\mathcal{D}, t\mathcal{D}) := (\Sigma\mathcal{D}, \{\Sigma a, a \in t\mathcal{D}\} \cup \operatorname{id}(\Sigma\mathcal{D}))$ the marked suspension of $(\mathcal{D}, t\mathcal{D})$.

Remark 2.7. By definition, given a marked $\infty$-category $(\mathcal{D}, t\mathcal{D})$, there is a canonical isomorphism in $\omega\mathcal{C}at$

$$U\Sigma(\mathcal{D}, t\mathcal{D}) \cong \Sigma\mathcal{D} \cong \Sigma U(\mathcal{D}, t\mathcal{D}).$$

**Proposition 2.8.** The functor $\Sigma: \omega\mathcal{C}at_{\text{coind}}^{+} \to \omega\mathcal{C}at_{\text{coind}}^{+}$ preserves acyclic cofibrations.

Proof. We say that

- a map of $\omega\mathcal{C}at_{*,*}^{+}$ is a fibration in $(\omega\mathcal{C}at_{\text{coind}}^{+})_{*,*}$ if it is one in $\omega\mathcal{C}at_{\text{coind}}^{+}$ when ignoring the base points;
- an object of $\omega\mathcal{C}at_{*,*}^{+}$ is fibrant in $(\omega\mathcal{C}at_{\text{coind}}^{+})_{*,*}$ if it is one in $\omega\mathcal{C}at_{\text{coind}}^{+}$ when ignoring the base points;
- a map of $\omega\mathcal{C}at_{*,*}^{+}$ is an acyclic cofibration in $(\omega\mathcal{C}at_{\text{coind}}^{+})_{*,*}$ if it has the left lifting property with respect to all fibrations between fibrant objects.

As a preliminary observation, we argue that the functor

$$U: (\omega\mathcal{C}at_{\text{coind}}^{+})_{*,*} \to \omega\mathcal{C}at_{\text{coind}}^{+}$$

preserves acyclic cofibrations. Let $j: (A, a, a') \to (B, b, b')$ be an acyclic cofibration in $(\omega\mathcal{C}at_{\text{coind}}^{+})_{*,*}$, and consider a lifting problem in $\omega\mathcal{C}at_{\text{coind}}^{+}$

![img-4.jpeg](img-4.jpeg)

This can be enhanced to a lifting problem in $(\omega\mathcal{C}at_{\text{coind}}^{+})_{*,*}$

![img-5.jpeg](img-5.jpeg)

14

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

This lifting problem admits a solution because, by definition, the left hand side map is an acyclic cofibration in  \( (\omega\mathcal{C}at_{\mathrm{coind}}^{+})_{*,*} \)  and the right hand side map is a fibration in  \( (\omega\mathcal{C}at_{\mathrm{coind}}^{+})_{*,*} \) .

Consider the adjunction

\[
\Sigma \colon \omega \mathcal {C} a t _ {\text {coind}} ^ {+} \leftrightarrows (\omega \mathcal {C} a t _ {\text {coind}} ^ {+}) _ {*, *} \text {:hom}.
\]

We first observe that the functor

\[
\mathrm{hom} \colon (\omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+}) _ {*, *} \to \omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+}
\]

preserves fibrant objects. To see this, one can use the characterization of fibrant objects from Theorem 2.4(3), and observe that given a marked \(\omega\)-category \(\mathcal{D}\) and \(a \in \mathrm{eq}_k\mathcal{D}\) for \(k > 1\), then \(a \in \mathrm{eq}_{k-1} \hom_{\mathcal{D}}(d_0^- a, d_0^+ a)\). Further, the functor

\[
\Sigma \colon \omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+} \to (\omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+}) _ {*, *}
\]

sends the marked \(\omega\)-functor \(i_n^+ \colon \mathcal{C}_n^\circ \hookrightarrow (\mathcal{C}_{n+1}, \{e_{n+1}\} \cup \mathrm{id}\mathcal{C}_{n+1})\) to the marked \(\omega\)-functor \(i_{n+1}^+ \colon \mathcal{C}_{n+1}^\circ \hookrightarrow (\mathcal{C}_{n+2}, \{e_{n+2}\} \cup \mathrm{id}\mathcal{C}_{n+2})\). Hence, by Theorem 2.4(5), the functor

\[
\mathrm{hom} \colon (\omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+}) _ {*, *} \to \omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+}
\]

preserves fibrations between fibrant objects. Finally, by definition of acyclic cofibrations and using the adjunction  \( \Sigma \dashv \)  hom, the functor

\[
\Sigma \colon \omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+} \to : (\omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+}) _ {*, *}
\]

preserves acyclic cofibrations, and so does the functor

\[
U \Sigma \colon \omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+} \to (\omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+}) _ {*, *} \to : \omega \mathcal {C} a t _ {\mathrm{coind}} ^ {+},
\]

as desired.

□

### 2.3. The marked model for the coherent  \( \omega \) -equivalence.

Construction 2.9. Let B, resp. A, denote the  \( \omega \) -category freely generated by the following datum

![img-6.jpeg](img-6.jpeg)

Let \((\mathcal{A}, t\mathcal{A})\), resp. \((\mathcal{B}, t\mathcal{B})\), denote the marked \(\omega\)-category for which \(t\mathcal{A}\), resp. \(t\mathcal{B}\), is minimal with the property that \(t\mathcal{A} \supseteq \mathrm{id}\mathcal{A} \cup \{f, \alpha\}\), resp. \(t\mathcal{B} \supseteq \mathrm{id}\mathcal{B} \cup \{f, \beta\}\). Let \((\overline{\mathcal{Q}}, t\overline{\mathcal{Q}})\) denote the marked \(\omega\)-category obtained as the pushout in \(\omega\mathcal{C}at^{+}\):

![img-7.jpeg](img-7.jpeg)

We refer the reader to [HL23, Construction 2.14] for a description of pushouts in \(\omega \mathcal{C}at^{+}\).

Lemma 2.10. The marked \(\omega\)-functor

\[
f \colon \mathcal {C} _ {1} ^ {\sharp} \to (\overline {{\mathcal {Q}}}, t \overline {{\mathcal {Q}}})
\]

is an acyclic cofibration in \(\omega \mathcal{C}at_{\mathrm{coind}}^{+}\).

A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

15

*Proof.* The marked $\omega$-functors

$$f: \mathcal{C}_1^\sharp \to (\mathcal{A}, t\mathcal{A}) \quad \text{and} \quad f: \mathcal{C}_1^\sharp \to (\mathcal{B}, t\mathcal{B})$$

can be recognized as equation inclusions (in the sense of [HL23, Definition 3.1]), so they are by [HL23, Corollary 3.24] acyclic cofibrations in the inductive left semi-model structure from [HL23, Corollary 2.38], hence in the left semi-model structure $\omega\mathcal{C}at_{\text{coind}}^+$, which was constructed as a left Bousfield localization of it (cf. Theorem 2.4). Furthermore, since acyclic cofibrations are closed under pushouts, the marked $\omega$-functor

$$(\mathcal{A}, t\mathcal{A}) \to (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}})$$

is also an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$, and hence so is the composite

$$f: \mathcal{C}_1^\sharp \to (\mathcal{A}, t\mathcal{A}) \to (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}),$$

as desired. $\square$

**Construction 2.11.** Let $(\overline{\omega\mathcal{E}}^{(0)}, t\overline{\omega\mathcal{E}}^{(0)}) := \mathcal{C}_1^\sharp$. For $k > 0$, we define inductively $(\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$ to be a marked $\omega$-category coming with a triple of marked $\omega$-functors

$$\overline{\tau}_k: (\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}),$$

$$\alpha_k, \beta_k: \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}).$$

- For $k = 1$, we let $(\overline{\omega\mathcal{E}}^{(1)}, t\overline{\omega\mathcal{E}}^{(1)}) := (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}})$, we let $\overline{\tau}_1$ be the marked $\omega$-functor

$$f: \mathcal{C}_1^\sharp \to (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}})$$

and $\alpha_1, \beta_1$ be defined by

$$\alpha_1: \Sigma p \mapsto g \begin{smallmatrix} \mathbb{Z} \\ 0\end{smallmatrix} f, \; \Sigma q \mapsto \text{id}_p, \; \Sigma f \mapsto \alpha \quad \text{and} \quad \beta_1: \Sigma p \mapsto f \begin{smallmatrix} \mathbb{Z} \\ 0\end{smallmatrix} g', \; \Sigma q \mapsto \text{id}_q, \; \Sigma f \mapsto \beta.$$

- For $k > 1$, we let $(\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$, $\overline{\tau}_k, \alpha_k$, and $\beta_k$ be defined by the pushout in $\omega\mathcal{C}at^+$ (2.12)

$$\begin{array}{ccc} \Sigma(\overline{\omega\mathcal{E}}^{(k-2)}, t\overline{\omega\mathcal{E}}^{(k-2)}) & \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-2)}, t\overline{\omega\mathcal{E}}^{(k-2)}) & \xrightarrow{[\alpha_{k-1}, \beta_{k-1}]} (\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \\ \Sigma(\overline{\tau}_{k-1}) \amalg \Sigma(\overline{\tau}_{k-1}) \updownarrow & & \updownarrow \overline{\tau}_k \\ \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) & \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) & \xrightarrow{[\alpha_k, \beta_k]} (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}). \end{array}$$

**Lemma 2.13.** *For all $k \geq 0$ the marked $\omega$-functor*

$$\overline{\tau}_k: (\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \hookrightarrow (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. In particular, $(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)})$ is cofibrant in $\omega\mathcal{C}at_{\text{coind}}^+$.

*Proof.* One can deduce this by induction on $k \geq 1$. The base case is Lemma 2.10, and the inductive step is a consequence of the induction hypothesis and (2.12). $\square$

**Construction 2.14.** We denote by $(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$ the colimit in $\omega\mathcal{C}at^+$ given by

$$(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) := \text{colim}[\cdots \leftrightarrow (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}) \leftrightarrow \cdots \leftrightarrow (\overline{\omega\mathcal{E}}^{(0)}, t\overline{\omega\mathcal{E}}^{(0)})].$$

16

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

**Lemma 2.15.** *Given $k \geq 0$, the marked $\omega$-functor*

$$\overline{\tau}_{k,\infty} : (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}) \hookrightarrow (\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$$

*obtained as a structure map in the colimit cone from Construction 2.14, is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^{+}$. In particular, $(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$ is cofibrant in $\omega\mathcal{C}at_{\text{coind}}^{+}$.*

*Proof.* This follows from Lemma 2.13, the fact that the class of acyclic cofibrations is closed under transfinite composition, and the fact that acyclic cofibrations are cofibrations. $\square$

We can understand the underlying $\omega$-category of $(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$:

**Lemma 2.16.** *Given $k \geq 0$, there exist $\omega$-functors*

$$\eta^{(k)} : \widehat{\omega\mathcal{E}}^{(k)} \to \overline{\omega\mathcal{E}}^{(k)} \quad \text{and} \quad \mu^{(k)} : \overline{\omega\mathcal{E}}^{(k)} \to \widehat{\omega\mathcal{E}}^{(k+1)}$$

*that make the following diagram in $\omega\mathcal{C}at$ commute:*

$$(2.17) \quad \begin{array}{c} \widehat{\omega\mathcal{E}}^{(k)} \xrightarrow{\iota_k} \widehat{\omega\mathcal{E}}^{(k+1)} \xrightarrow{\iota_{k+1}} \widehat{\omega\mathcal{E}}^{(k+2)} \\ \searrow_{\eta^{(k)}} \searrow_{\overline{\omega\mathcal{E}}^{(k)}} \searrow_{\eta^{(k)}} \searrow_{\eta^{(k+1)}} \searrow_{\overline{\omega\mathcal{E}}^{(k+1)}} \end{array}$$

*Proof.* We construct the $\omega$-functors $\eta^{(k)}$ and $\mu^{(k)}$ by induction on $k \geq 0$. For the base cases, we set $\eta^{(0)}$ and $\mu^{(0)}$ to be the $\omega$-functors

$$\eta^{(0)} : \widehat{\omega\mathcal{E}}^{(0)} = \partial\mathcal{C}_1 \hookrightarrow \mathcal{C}_1 = \overline{\omega\mathcal{E}}^{(0)} \quad \text{and} \quad \mu^{(0)} : \overline{\omega\mathcal{E}}^{(0)} = \mathcal{C}_1 \xrightarrow{f_1} \mathcal{Q} = \widehat{\omega\mathcal{E}}^{(1)},$$

and we set $\eta^{(1)}$ and $\mu^{(1)}$ to be the unique $\omega$-functors

$$\eta^{(1)} : \widehat{\omega\mathcal{E}}^{(1)} = \mathcal{Q} \hookrightarrow \overline{\mathcal{Q}} = \overline{\omega\mathcal{E}}^{(1)} \quad \text{and} \quad \mu^{(1)} : \overline{\omega\mathcal{E}}^{(1)} = \overline{\mathcal{Q}} \to \widehat{\omega\mathcal{E}}^{(2)},$$

which are identity on underlying 1-categories and such that

$$\mu^{(1)} : \alpha \mapsto \alpha_1(\Sigma f) \quad \text{and} \quad \mu^{(1)} : \beta \mapsto \beta_1(\Sigma f).$$

For the inductive step, we assume that $\eta^{(k)}$ and $\mu^{(k)}$ have been constructed, and we now construct $\eta^{(k+1)}$ and $\mu^{(k+1)}$. Using Remark 2.7 and Proposition 2.3 and (2.12), we see that there is a commutative diagram in $\omega\mathcal{C}at$:

$$\begin{array}{ccc} \Sigma(\widehat{\omega\mathcal{E}}^{(k)}) \amalg \Sigma(\widehat{\omega\mathcal{E}}^{(k)}) & \longleftarrow & \Sigma(\widehat{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma(\widehat{\omega\mathcal{E}}^{(k-1)}) \longrightarrow \widehat{\omega\mathcal{E}}^{(k)} \\ & \downarrow \Sigma\eta^{(k)} \amalg \Sigma\eta^{(k)} & \downarrow \Sigma\eta^{(k-1)} \amalg \Sigma\eta^{(k-1)} & \downarrow \eta^{(k)} \\ \Sigma(\overline{\omega\mathcal{E}}^{(k)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k)}) & \longleftarrow & \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}) \longrightarrow \overline{\omega\mathcal{E}}^{(k)} \end{array}$$

and, using (2.12), we define $\eta^{(k+1)}$ as the $\omega$-functor

$$\eta^{(k+1)} : \widehat{\omega\mathcal{E}}^{(k+1)} \to \overline{\omega\mathcal{E}}^{(k+1)}$$

induced at the level of colimits by this map of spans in $\omega\mathcal{C}at$. Similarly, using again Remark 2.7 and Proposition 2.3 and (2.12), we see that there is a commutative

A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

17

diagram in $\omega\mathcal{C}at$:

$$\begin{array}{c} \Sigma(\overline{\omega\mathcal{E}}^{(k)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k)}) \longleftarrow \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}) \longrightarrow \overline{\omega\mathcal{E}}^{(k)} \\ \downarrow_{\Sigma\mu^{(k)}\amalg\Sigma\mu^{(k)}} \qquad \qquad \downarrow_{\Sigma\mu^{(k-1)}\amalg\Sigma\mu^{(k-1)}} \qquad \qquad \downarrow_{\mu^{(k)}} \\ \Sigma(\widehat{\omega\mathcal{E}}^{(k+1)}) \amalg \Sigma(\widehat{\omega\mathcal{E}}^{(k+1)}) \longleftarrow \Sigma(\widehat{\omega\mathcal{E}}^{(k)}) \amalg \Sigma(\widehat{\omega\mathcal{E}}^{(k)}) \longrightarrow \widehat{\omega\mathcal{E}}^{(k+1)} \end{array}$$

and, using (2.12), we define $\mu^{(k+1)}$ as the $\omega$-functor

$$\mu^{(k+1)}: \overline{\omega\mathcal{E}}^{(k+1)} \to \widehat{\omega\mathcal{E}}^{(k+2)}$$

induced at the level of colimits by this map of spans in $\omega\mathcal{C}at$. One can finally show, by induction on $k \ge 0$, that the $\omega$-functors $\eta^{(k)}$, $\mu^{(k)}$, $\eta^{(k+1)}$ and $\mu^{(k+1)}$ fit into the desired commutative diagram in $\omega\mathcal{C}at$. $\square$

**Proposition 2.18.** *There is an isomorphism in $\omega\mathcal{C}at*

$$\mu: \overline{\omega\mathcal{E}} = U(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) \cong \widehat{\omega\mathcal{E}}: \eta.$$

*Proof.* From the property (2.17), one can deduce that the $\omega$-functors $\eta^{(k)}$ and $\mu^{(k)}$ from Lemma 2.16 define by construction the components of two natural transformations with respect to $k \in \mathbb{N}$. By taking the $\omega$-functor induced at the level of colimits over $n \in \mathbb{N}$ we then obtain $\omega$-functors

$$\underset{k \in \mathbb{N}}{\text{colim}} \eta^{(k)}: \underset{k \in \mathbb{N}}{\text{colim}} \widehat{\omega\mathcal{E}}^{(k)} \to \underset{k \in \mathbb{N}}{\text{colim}} \overline{\omega\mathcal{E}}^{(k)}, \quad \underset{k \in \mathbb{N}}{\text{colim}} \mu^{(k)}: \underset{k \in \mathbb{N}}{\text{colim}} \overline{\omega\mathcal{E}}^{(k)} \to \underset{k \in \mathbb{N}}{\text{colim}} \widehat{\omega\mathcal{E}}^{(k+1)},$$

which can be identified with $\omega$-functors

$$\eta: \widehat{\omega\mathcal{E}} \to \overline{\omega\mathcal{E}} \quad \text{and} \quad \mu: \overline{\omega\mathcal{E}} \to \widehat{\omega\mathcal{E}}.$$

From the property (2.17), one can also deduce that $\mu$ and $\eta$ are inverse to each other, concluding the proof. $\square$

**Lemma 2.19.** *The inverse isomorphisms $\mu$ and $\eta$ in $\omega\mathcal{C}at$ induce inverse isomorphisms in $\omega\mathcal{C}at^{+}$*

$$\mu: \overline{\omega\mathcal{E}}^{\sharp} = \overline{\omega\mathcal{E}}^{\sharp} \cong \widehat{\omega\mathcal{E}}^{\sharp} = \widehat{\omega\mathcal{E}}^{\sharp}: \eta.$$

*Proof.* Since $(-)^{\sharp}$ is a functor we obtain inverse isomorphisms in $\omega\mathcal{C}at^{+}$

$$\mu: \overline{\omega\mathcal{E}}^{\sharp} \cong \widehat{\omega\mathcal{E}}^{\sharp}: \eta.$$

By Propositions 1.19 and 1.32, all cells of $\widehat{\omega\mathcal{E}}$ above dimension 0 are $\omega$-equivalences, which implies that

$$\widehat{\omega\mathcal{E}}^{\sharp} = \widehat{\omega\mathcal{E}}^{\sharp}.$$

By Proposition 2.18 we obtain that

$$\overline{\omega\mathcal{E}}^{\sharp} = \overline{\omega\mathcal{E}}^{\sharp}.$$

This concludes the proof. $\square$

**Proposition 2.20.** *The $\omega$-functor $\mu$ determines an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^{+}$*

$$\mu: (\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) \hookrightarrow \overline{\omega\mathcal{E}}^{\sharp} \cong \widehat{\omega\mathcal{E}}^{\sharp}$$

18

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

Proof. The existence of the marked $\omega$-functor follows from Lemma 2.19 and the adjunction $U \dashv (-)^\sharp$, and the fact that it is an acyclic cofibration follows from Lemma 2.5 and Proposition 2.18. $\square$

**Lemma 2.21.** Given $k \geq 0$, the marked $\omega$-functor

$$f_k \colon \mathcal{C}_1^\sharp \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. In particular, by two-out-of-three for weak equivalences in $\omega\mathcal{C}at_{\text{coind}}^+$, we obtain that the marked $\omega$-functor

$$\overline{\iota}_k \colon (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}) \to (\overline{\omega\mathcal{E}}^{(k+1)}, t\overline{\omega\mathcal{E}}^{(k+1)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$.

Proof. We prove this by induction on $k \geq 1$. The base case $k = 1$ is Lemma 2.10, and we now show the induction step, assuming the statement to be true for $k - 1$. We have that the marked $\omega$-functor

$$f_{k-1} \colon \mathcal{C}_1^\sharp \to (\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. By Proposition 2.8, we obtain that the marked $\omega$-functor

$$\Sigma\mathcal{C}_1^\sharp \amalg \Sigma\mathcal{C}_1^\sharp \to \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)}) \amalg \Sigma(\overline{\omega\mathcal{E}}^{(k-1)}, t\overline{\omega\mathcal{E}}^{(k-1)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. By closure of the class of acyclic cofibrations under pushouts, we obtain that the marked $\omega$-functor

$$(\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$. By Lemma 2.10, we obtain that the composite marked $\omega$-functor

$$f_k \colon \mathcal{C}_1^\sharp \xrightarrow{f_1} (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)})$$

is an acyclic cofibration in $\omega\mathcal{C}at_{\text{coind}}^+$, as desired. $\square$

**Proposition 2.22.** The unique marked $\omega$-functor

$$(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) \to \mathcal{C}_0^\sharp$$

is a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$.

Proof. The marked $\omega$-functor

$$i_0^+ \colon \mathcal{C}_0^\sharp \hookrightarrow \mathcal{C}_1^\sharp$$

is by Theorem 2.4 a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$. The marked $\omega$-functor

$$f_1 \colon \mathcal{C}_1^\sharp \hookrightarrow (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}})$$

is a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$ by Lemma 2.10. The marked $\omega$-functor

$$(\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}) \to (\overline{\omega\mathcal{E}}^{(k)}, t\overline{\omega\mathcal{E}}^{(k)}) \to (\overline{\omega\mathcal{E}}^{(k+1)}, t\overline{\omega\mathcal{E}}^{(k+1)}) \to \dots \to (\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$$

is a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$ by Lemma 2.21, using the fact that acyclic cofibrations are closed under transfinite composition. So the composite marked $\omega$-functor

$$\mathcal{C}_0^\sharp \xrightarrow{i_0^+} \mathcal{C}_1^\sharp \xrightarrow{f_1} (\overline{\mathcal{Q}}, t\overline{\mathcal{Q}}) \to (\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}})$$

is a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$. By two-out-of-three, the unique $\omega$-functor

$$(\overline{\omega\mathcal{E}}, t\overline{\omega\mathcal{E}}) \to \mathcal{C}_0^\sharp$$

A MODEL FOR THE COHERENT WALKING $\omega$-EQUIVALENCE

19

is then also a weak equivalence in $\omega\mathcal{C}at_{\text{coind}}^+$, as desired. $\square$

We can finally now prove the main theorem, namely that the unique morphism $\widehat{\omega\mathcal{E}} \to \mathcal{C}_0$ is a weak equivalence in $\omega\mathcal{C}at_{\text{can}}$:

*Proof of Theorem 1.33.* Consider the commutative diagram in $\omega\mathcal{C}at_{\text{coind}}^+$

![img-8.jpeg](img-8.jpeg)

By Propositions 2.20 and 2.22, the top and the diagonal marked $\omega$-functors are weak equivalences in $\omega\mathcal{C}at_{\text{coind}}^+$. By two-out-of-three, so is the right vertical marked $\omega$-functor

$$\widehat{\omega\mathcal{E}}^\sharp \to \mathcal{C}_0^\sharp.$$

By Theorem 2.4(3), the marked $\omega$-categories $\widehat{\omega\mathcal{E}}^\sharp$ and $\mathcal{C}_0^\sharp$ are fibrant in $\omega\mathcal{C}at_{\text{coind}}^+$. By Theorem 2.4(4), the forgetful functor $U: \omega\mathcal{C}at_{\text{coind}}^+ \to \omega\mathcal{C}at_{\text{can}}$ preserves weak equivalences between fibrant objects, so the unique $\omega$-functor

$$\widehat{\omega\mathcal{E}} = U(\widehat{\omega\mathcal{E}}^\sharp) \to U(\mathcal{C}_0^\sharp) = U(\mathcal{C}_0^\sharp) = \mathcal{C}_0$$

is a weak equivalence in $\omega\mathcal{C}at_{\text{can}}$, as desired. $\square$

# REFERENCES

[ABG$^+$23] Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François Métayer, and Samuel Mimram, *Polygraphs: From rewriting to higher categories*, arXiv:2312.00429v1, 2023. 1, 2, 3, 11
[AL20] Dimitri Ara and Maxime Lucas, *The folk model category structure on strict $\omega$-categories is monoidal*, Theory Appl. Categ. **35** (2020), Paper No. 21, 745–808. 2, 4
[AM20] Dimitri Ara and Georges Maltsiniotis, *Joint et tranches pour les $\infty$-catégories strictes*, Mém. Soc. Math. Fr. (N.S.) (2020), no. 165, vi+213. 1, 2, 3
[BW24] Michael Batanin and David White, *Left Bousfield localization without left properness*, J. Pure Appl. Algebra **228** (2024), no. 6, Paper No. 107570, 23. 12
[Che07] Eugenia Cheng, *An $\omega$-category with all duals is an $\omega$-groupoid*, Applied Categorical Structures **15** (2007), 439–453. 2
[cli22] tslil clingman, *Towards the theory of proof-relevant categories*, Ph.D. thesis, Johns Hopkins University, 2022. 2
[FHM23] Soichiro Fujii, Keisuke Hoshino, and Yuki Maehara, *Weakly invertible cells in a weak $\omega$-category*, arXiv:2303.14907v2, 2023. 1, 2
[Gol23] Zach Goldthorpe, *Homotopy theories of $(\infty, \infty)$-categories as universal fixed points with respect to weak enrichment*, Int. Math. Res. Not. IMRN (2023), no. 22, 19592–19640. 1
[Gol24] Zach Goldthorpe, *Sheaves of $(\infty, \infty)$-categories*, arXiv:2403.06926v3, 2024. 1
[Gur12] Nick Gurski, *Biequivalences in tricategories*, Theory Appl. Categ. **26** (2012), No. 14, 349–384. 2
[Had20] Amar Hadzihasanovic, *Diagrammatic sets and rewriting in weak higher categories*, arXiv:2007.14505v1, 2020. 2
[Hen20] Simon Henry, *Weak model categories in classical and constructive mathematics*, Theory Appl. Categ. **35** (2020), Paper No. 24, 875–958. 12
[Hen23] ______, *Combinatorial and accessible weak model categories*, J. Pure Appl. Algebra **227** (2023), no. 2, Paper No. 107191, 46. 12
[Hir21] Philip S. Hirschhorn, *Overcategories and undercategories of cofibrantly generated model categories*, J. Homotopy Relat. Struct. **16** (2021), no. 4, 753–768. 3

20

HADZIHASANOVIC, LOUBATON, OZORNOVA, AND ROVELLI

[HL23] Simon Henry and Félix Loubaton, An inductive model structure for strict ∞-categories, arXiv:2301.11424v1, 2023. 2, 11, 12, 14, 15
[HORR23] Philip Hackney, Viktoriya Ozornova, Emily Riehl, and Martina Rovelli, An (∞, 2)-categorical pasting theorem, Trans. Amer. Math. Soc. 376 (2023), no. 1, 555–597. 1
[Lac02] Stephen Lack, A Quillen model structure for 2-categories, K-Theory 26 (2002), no. 2, 171–205. 2
[Lac04] ______, A Quillen model structure for bicategories, K-Theory 33 (2004), no. 3, 185–197. 2
[LMW10] Yves Lafont, François Métayer, and Krzysztof Worytkiewicz, A folk model structure on omega-cat, Advances in Mathematics 224 (2010), no. 3, 1183–1231. 1, 2, 3, 4, 8
[Lou23] Félix Loubaton, Kan conditions on the nerves of ω-categories, Bull. Soc. Math. Fr. 151 (2023), no. 2, 331–406 (French). 2, 4
[OR21] Viktoriya Ozornova and Martina Rovelli, Nerves of 2-categories and 2-categorification of (∞, 2)-categories, Advances in Mathematics 391 (2021), 107948. 2
[OR23] ______, A Quillen adjunction between globular and complicial approaches to (∞, n)-categories, Adv. Math. 421 (2023), Paper No. 108980, 57. 3
[OR24] ______, What is an equivalence in a higher category?, Bulletin of the London Mathematical Society 56 (2024), no. 1, 1–58. 1, 2
[Rez10] Charles Rezk, A Cartesian presentation of weak n-categories, Geom. Topol. 14 (2010), no. 1, 521–571. 1
[Ric20] Alex Rice, Coinductive invertibility in higher categories, arXiv:2008.10307v2, 2020. 2, 4, 5, 7
[RV16] Emily Riehl and Dominic Verity, Homotopy coherent adjunctions and the formal theory of monads, Adv. Math. 286 (2016), 802–888. 1
[Ste04] Richard Steiner, Omega-categories and chain complexes, Homology Homotopy Appl. 6 (2004), no. 1, 175–200. 1
[Str87] Ross Street, The algebra of oriented simplexes, J. Pure Appl. Algebra 49 (1987), no. 3, 283–335. 1
[Ver08] Dominic Verity, Weak complicial sets. I. Basic homotopy theory, Adv. Math. 219 (2008), no. 4, 1081–1149. 1

TALLINN UNIVERSITY OF TECHNOLOGY, TALLINN, ESTONIA
Email address: amar.hadzihasanovic@taltech.ee

MAX PLANCK INSTITUTE FOR MATHEMATICS, BONN, GERMANY
Email address: loubaton@mpim-bonn.mpg.de

MAX PLANCK INSTITUTE FOR MATHEMATICS, BONN, GERMANY
Email address: viktoriya.ozornova@mpim-bonn.mpg.de

UNIVERSITY OF MASSACHUSETTS AMHERST, AMHERST (MA), USA
Email address: mrovelli@umass.edu