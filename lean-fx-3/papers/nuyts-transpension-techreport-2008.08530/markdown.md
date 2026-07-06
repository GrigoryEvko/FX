arXiv:2008.08530v4 [cs.LO] 23 May 2024

# The Transpension Type: Technical Report

Andreas Nuyts\*  
DistriNet, KU Leuven, Belgium

May 24, 2024

## Contents

|  **1** | **Introduction** | **2**  |
| --- | --- | --- |
|  **2** | **Prerequisites** | **2**  |
|  2.1 | On adjoints | 2  |
|  2.1.1 | Adjoints and natural transformations | 2  |
|  2.1.2 | Adjoints and categories with families | 3  |
|  2.1.3 | Adjoints and slice categories | 3  |
|  2.2 | Dependent ends and co-ends | 4  |
|  2.3 | Presheaves | 4  |
|  2.3.1 | Notation | 4  |
|  2.3.2 | On the Yoneda-embedding | 5  |
|  2.3.3 | Lifting functors | 5  |
|  2.3.4 | Dependent presheaf categories | 6  |
|  2.3.5 | Substitution and its adjoints | 7  |
|  2.3.6 | Reconstructing right adjoints | 9  |
|  **3** | **Multipliers in the base category** | **10**  |
|  3.1 | Definition | 10  |
|  3.2 | Basic properties | 10  |
|  3.3 | Examples | 11  |
|  3.4 | Properties | 15  |
|  3.4.1 | Functoriality | 15  |
|  3.4.2 | Quantification and quotient theorem | 16  |
|  3.4.3 | Dealing with unpointability | 17  |
|  3.4.4 | Boundaries | 18  |
|  3.5 | Acting on slice objects | 19  |
|  3.6 | Composing multipliers | 23  |
|  **4** | **Multipliers and presheaves** | **25**  |
|  4.1 | Acting on elements | 25  |
|  4.2 | Acting on presheaves | 30  |
|  4.3 | Four adjoint functors | 32  |
|  4.4 | Investigating the transpension functor | 33  |
|  **5** | **Prior modalities** | **39**  |

\*Andreas Nuyts holds a Postdoctoral Fellowship from the Research Foundation - Flanders (FWO; 1247922N), and carried out most of this research holding a PhD Fellowship from the Research Foundation - Flanders (FWO; 1110817N). This research was partially conducted at Vrije Universiteit Brussel and funded by the Research Foundation - Flanders (FWO; G0G0519N). This research is partially funded by the Research Fund KU Leuven.

1

# 6 Commutation rules 40

6.1 Substitution and substitution 40
6.2 Modality and substitution 40
6.3 Multiplier and substitution 41
6.4 Multiplier and modality 42
6.5 Multiplier and multiplier 43

# A Changelog 45

A.1 Definition 3.1.1 45
A.2 Definition 3.1.2 45
A.3 Definition 3.4.1 45
A.4 Quotient theorem 46
A.5 Definition 3.5.1 46
A.6 Definition 4.1.1 46

# 1 Introduction

The purpose of these notes is to give a categorical semantics for the transpension type [ND24], which is right adjoint to a potentially substructural dependent function type.

- In section 2 we discuss some prerequisites.
- In section 3, we define multipliers and discuss their properties.
- In section 4, we study how multipliers lift from base categories to presheaf categories.
- In section 5, we explain how typical presheaf modalities can be used in the presence of the transpension type.
- In section 6, we study commutation properties of prior modalities, substitution modalities and multiplier modalities.

# 2 Prerequisites

## 2.1 On adjoints

### 2.1.1 Adjoints and natural transformations

Lemma 2.1.1. Let $L \dashv R$.

- Natural transformations $LF \to G$ correspond to natural transformations $F \to RG$, naturally in $F$ and $G$.
- Natural transformations $FR \to G$ correspond to natural transformations $F \to GL$, naturally in $F$ and $G$.

Proof. The first statement is trivial.

To see the second statement, we send $\zeta : FR \to G$ to $\zeta L \circ F\eta : F \to GL$, and conversely $\theta : F \to GL$ to $G\varepsilon \circ \theta R : FR \to G$. Naturality is clear. Mapping $\zeta$ to and fro, we get

$$G\varepsilon \circ \zeta LR \circ F\eta R = \zeta \circ FR\varepsilon \circ F\eta R = \zeta. \tag{1}$$

Mapping $\theta$ to and fro, we get

$$G\varepsilon L \circ \theta RL \circ F\eta = G\varepsilon L \circ GL\eta \circ \theta = \theta. \tag{\square}$$

2

Lemma 2.1.2. Assume 4 triples of adjoint functors: \( E \dashv F \dashv G \) and \( E' \dashv F' \dashv G' \) and \( S_1 \dashv T_1 \dashv U_1 \) and \( S_2 \dashv T_2 \dashv U_2 \) such that the following diagram commutes up to natural isomorphism:

\[
\begin{array}{c} \mathcal {C} _ {1} \xrightarrow {F} \mathcal {C} _ {2} \\ T _ {1} \Bigg \downarrow \quad \Bigg \downarrow T _ {2} \\ \mathcal {C} _ {1} ^ {\prime} \xrightarrow [ F ^ {\prime} ]{} \mathcal {C} _ {2} ^ {\prime} \end{array} \tag {2}
\]

Then we have

\[
\begin{array}{l} E S _ {2} \cong S _ {1} E ^ {\prime} \quad E ^ {\prime} T _ {2} \rightarrow T _ {1} E \\ F S _ {1} \leftarrow S _ {2} F ^ {\prime} \quad F ^ {\prime} T _ {1} \cong T _ {2} F \quad F U _ {1} \rightarrow U _ {2} F ^ {\prime} \tag {3} \\ G ^ {\prime} T _ {2} \leftarrow T _ {1} G \quad G U _ {2} \cong U _ {1} G ^ {\prime}. \\ \end{array}
\]

In fact, any one of these statements holds if only the adjoints used by that statement are given.

Proof. The central isomorphism is given. The other isomorphisms are obtained by taking the left/right adjoints of both hands of the original isomorphism. By picking one direction of the central isomorphism, we can step to the left/right/top/bottom by applying lemma 2.1.1. \(\square\)

#### 2.1.2 Adjoints and categories with families

Proposition 2.1.3. If a functor \( R: \mathcal{C} \to \widehat{\mathcal{W}} \) from a CwF \( \mathcal{C} \) to a presheaf CwF \( \widehat{\mathcal{W}} \) has a left adjoint \( L \), then it is a weak CwF morphism.

Proof. We use the presheaf notations from [Nuy18] (section 2.3.1).

For \(\Gamma \vdash_{\mathcal{C}} T\) type, define \(R\Gamma \vdash_{\widehat{\mathcal{W}}} RT\) type by

\[
(W \triangleright_ {\widehat {\mathcal {W}}} (R T) [ \delta ]) := \cong (L \mathbf {y} W \vdash_ {\mathcal {C}} T [ \varepsilon \circ L \delta ]). \tag {4}
\]

Naturality of this operation is easy to show, and the action of \( R \) on terms is given by \( (^R t)[\delta] = t[\varepsilon \circ L\delta] \).

Definition 2.1.4. Given adjoint functors \( L \dashv R \) such that \( R \) is a weak CwF morphism, and \( A \in \mathrm{Ty}(L\Gamma) \), we write \( \langle R|A\rangle := (RA)[\eta] \in \mathrm{Ty}(\Gamma) \).

Note that \(\langle R|A[\varepsilon]\rangle = (RA)[R\varepsilon][\eta] = RA\).

#### 2.1.3 Adjoints and slice categories

Definition 2.1.5. For any \(U \in \mathcal{W}\), the slice category over \(U\), denoted \(\mathcal{W}/U\), has objects \((W, \psi)\) where \(W \in \mathcal{W}\) and \(\psi: W \to U\) and the morphisms \((W, \psi) \to (W', \psi')\) are the morphisms \(\chi: W \to W'\) such that \(\psi' \circ \chi = \psi\).

Definition 2.1.6. Given a functor \( F: \mathcal{V} \to \mathcal{W} \) and \( V_0 \in \mathrm{Obj}\mathcal{V} \), we define the action of \( F \) on slice objects over \( V_0 \) as the functor

\[
F ^ {/ V _ {0}}: \mathcal {V} / V _ {0} \to \mathcal {W} / F V _ {0}: (V, \varphi) \mapsto (F V, F \varphi).
\]

Proposition 2.1.7. Let \( L \dashv R : \mathcal{C} \to \mathcal{D} \) with \( \alpha : \mathrm{Hom}_{\mathcal{C}}(Lc, d) \cong \mathrm{Hom}_{\mathcal{D}}(c, Rd).^1 \). Then \( R^{/z} : \mathcal{C}/c_0 \to \mathcal{D}/Rc_0 : (c, \gamma) \mapsto (Rc, R\gamma) \) has a left adjoint \( L_{/z} : \mathcal{D}/Rc_0 \to \mathcal{C}/c_0 : (d, \delta) \mapsto (Ld, \alpha^{-1}(\delta)) \). The transposition operation is simply the restriction of \( \alpha \) to morphisms of slice objects.

Proof. There is a 1-1 correspondence between diagrams

![img-0.jpeg](img-0.jpeg)

![img-1.jpeg](img-1.jpeg)

\( ^{1} \) So  \( \alpha(\gamma)=R\gamma\circ\eta \)  and  \( \alpha^{-1}(\delta)=\varepsilon\circ L\delta \) .

3

## 2.2 Dependent ends and co-ends

We will use $\forall$ and $\exists$ to denote ends and co-ends as well as their dependent generalizations [Nuy20, §2.2.6-7]:

**Definition 2.2.1.** A **dependent end** of a functor $F : \text{Tw}(\mathcal{I}) \rightarrow \mathcal{C}$, somewhat ambiguously denoted $\forall i.F(i \xrightarrow{\text{id}} i)$, is a limit of $F$.

**Definition 2.2.2.** A **dependent co-end** of a functor $F : \text{Tw}(\mathcal{I})^{\text{op}} \rightarrow \mathcal{C}$, somewhat ambiguously denoted $\exists i.F(i \xrightarrow{\text{id}} i)$, is a colimit of $F$.

**Example 2.2.3.** Assume a functor $G : \mathcal{C} \rightarrow \mathcal{D}$. One way to denote the set of natural transformations $\text{Id}_\mathcal{C} \rightarrow \text{Id}_\mathcal{C}$ which map to the identity under $G$, is as

$$A := \forall (c \in \mathcal{C}). \{\chi : c \rightarrow c \mid G\chi = \text{id}_{Gc}\}.$$

In order to read the above as a dependent end, we must find a functor $G : \text{Tw}(\mathcal{C}) \rightarrow \text{Set}$ such that $G(c \xrightarrow{\text{id}} c) = \{\chi : c \rightarrow c \mid G\chi = \text{id}_{Gc}\}$. Clearly every covariant occurrence of $c$ refers to the codomain of $(c \xrightarrow{\text{id}} c)$, whereas every contravariant occurrence refers to the domain. So when we apply $G$ to a general object $(x \xrightarrow{\varphi} y)$ of $\text{Tw}(\mathcal{C})$, we should substitute $x$ for every contravariant $c$ and $y$ for every covariant $c$. We can then throw in $\varphi$ wherever this is necessary to keep things well-typed, as $\varphi$ disappears anyway when $(x \xrightarrow{\varphi} y) = (c \xrightarrow{\text{id}} c)$. Thus, we get

$$G(x \xrightarrow{\varphi} y) = \{\chi : x \rightarrow y \mid G\chi = G\varphi\}.$$

So we see that using a *dependent* end was necessary in order to mention $\text{id}_c$, as this generalizes to $\varphi : x \rightarrow y$ to which we do not have access in a non-dependent end.

An element of $\nu \in A$ is then a function

$$\nu : (c \in \mathcal{C}) \rightarrow \{\chi : c \rightarrow c \mid G\chi = \text{id}_{Gc}\}$$

such that, whenever $\varphi : x \rightarrow y$, we have $\varphi \circ \nu_x = \nu_y \circ \varphi$.

## 2.3 Presheaves

### 2.3.1 Notation

We use the presheaf notations from [Nuy18]. Concretely:

- The application of a presheaf $\Gamma \in \widehat{\mathcal{W}}$ to an object $W \in \mathcal{W}$ is denoted $W \Rightarrow \Gamma$.
- The restriction of $\gamma : W \Rightarrow \Gamma$ by $\varphi : V \rightarrow W$ is denoted $\gamma \circ \varphi$ or $\gamma\varphi$.
- The application of a presheaf morphism $\sigma : \Gamma \rightarrow \Delta$ to $\gamma : W \Rightarrow \Gamma$ is denoted $\sigma \circ \gamma$ or $\sigma\gamma$.
  - By naturality of $\sigma$, we have $\sigma \circ (\gamma \circ \varphi) = (\sigma \circ \gamma) \circ \varphi$.
- If $\Gamma \in \widehat{\mathcal{W}}$ and $T \in \text{Ty}(\Gamma)$ (also denoted $\Gamma \vdash T$ type), i.e. $T$ is a presheaf over the category of elements $\mathcal{W}/\Gamma$, then we write the application of $T$ to $(W, \gamma)$ as $(W \triangleright T[\gamma])$ and $t \in (W \triangleright T[\gamma])$ as $W \triangleright t : T[\gamma]$.
  - By definition of type substitution in a presheaf CwF, we have $(W \triangleright T[\sigma][\gamma]) = (W \triangleright T[\sigma\gamma])$
- The restriction of $W \triangleright t : T[\gamma]$ by $\varphi : (V, \gamma \circ \varphi) \rightarrow (W, \gamma)$ is denoted as $W \triangleright t \langle \varphi \rangle : T[\gamma\varphi]$.
- If $t \in \text{Tm}(\Gamma, T)$ (also denoted $\Gamma \vdash t : T$), then the application of $t$ to $(W, \gamma)$ is denoted $V \triangleright t[\gamma] : T[\gamma]$.
  - The naturality condition for terms is then expressed as $t[\gamma] \langle \varphi \rangle = t[\gamma\varphi]$.

4

- By definition of term substitution in a presheaf CwF, we have $t[\sigma][\gamma] = t[\sigma\gamma]$.

- We omit applications of the isomorphisms $(W \Rightarrow \Gamma) \cong (\mathbf{y}W \to \Gamma)$ and $(W \triangleright T[\gamma]) \cong (\mathbf{y}W \vdash T[\gamma])$. This is not confusing: e.g. given $W \triangleright t : T[\gamma]$, the term $\mathbf{y}W \vdash t' : T[\gamma]$ is defined by $t'[\varphi] := t \langle \varphi \rangle$.

One advantage of these notations is that we can put presheaf cells in diagrams; we will use double arrows when doing so.

### 2.3.2 On the Yoneda-embedding

We consider the Yoneda-embedding $\mathbf{y} : \mathcal{W} \to \widehat{\mathcal{W}}$.

**Proposition 2.3.1.** A morphism $\varphi : V \to W$ in $\mathcal{W}$ is:

- Mono if and only if $\mathbf{y}\varphi$ is mono,
- Split epi if and only if $\mathbf{y}\varphi$ is epi.

*Proof.* It is well-known that a presheaf morphism $\sigma : \Gamma \to \Delta$ is mono/epi if and only if $\sigma \circ \sqcup : (W \Rightarrow \Gamma) \to (W \Rightarrow \Delta)$ is injective/surjective for all $W$. Now $\mathbf{y}\varphi \circ \sqcup = \varphi \circ \sqcup$. So $\mathbf{y}\varphi$ is mono if and only if $\varphi \circ \sqcup$ is injective, which means $\varphi$ is mono. On the other hand, $\mathbf{y}\varphi$ is epi if and only if $\varphi \circ \sqcup$ is surjective, which is the case precisely when id is in its image, and that exactly means that $\varphi$ is split epi. $\square$

### 2.3.3 Lifting functors

**Theorem 2.3.2.** Any functor $F : \mathcal{V} \to \mathcal{W}$ gives rise to functors $F_! \dashv F^* \dashv F_*$, with a natural isomorphism $F_! \circ \mathbf{y} \cong \mathbf{y} \circ F : \mathcal{V} \to \widehat{\mathcal{W}}$. We will call $F_! : \widehat{\mathcal{V}} \to \widehat{\mathcal{W}}$ the **left lifting** of $F$ to presheaves, $F^* : \widehat{\mathcal{W}} \to \widehat{\mathcal{V}}$ the **central** and $F_* : \widehat{\mathcal{V}} \to \widehat{\mathcal{W}}$ the **right lifting**.$^{23}$ [Sta19]

*Proof.* Using quantifier symbols for ends and co-ends, we can define:

$$\begin{aligned} W \Rightarrow F_! \Gamma & := \exists V.(W \to FV) \times (V \Rightarrow \Gamma), \\ V \Rightarrow F^* \Delta & := FV \Rightarrow \Delta \\ W \Rightarrow F_* \Gamma & := \forall V.(FV \to W) \to (V \Rightarrow \Gamma) = (F^* \mathbf{y}W \to \Gamma). \end{aligned}$$

By the co-Yoneda lemma, we have:

$$W \Rightarrow F_! \mathbf{y}V = \exists V'.(W \to FV') \times (V' \to V) \cong (W \to FV) = (W \Rightarrow \mathbf{y}FV),$$

i.e. $F_! \mathbf{y}V \cong \mathbf{y}FV$.

Adjointness also follows from applications of the Yoneda and co-Yoneda lemmas. $\square$

**Notation 2.3.3.** • We denote the cell $(V, \varphi, \gamma) : W \Rightarrow F_! \Gamma$ as $F_! \gamma \circ \varphi$. If we rename $F_!$, then we will also do so in this notation. We will further abbreviate $F_! \gamma \circ \text{id} = F_! \gamma$ and, if $\Gamma = \mathbf{y}V$, also $F_! \text{id} \circ \varphi = \varphi$.

- If $\delta : FV \Rightarrow \Delta$, then we write $\alpha_F(\delta) : V \Rightarrow F^* \Delta$.
- If $\gamma : F^* \mathbf{y}W \to \Gamma$, then we write $\beta_F(\gamma) : W \Rightarrow F_* \Gamma$.

**Proposition 2.3.4.** A functor $F : \mathcal{V} \to \mathcal{W}$ is fully faithful if and only if $F_!$ is fully faithful.

$^2$The central and right liftings are also sometimes called the inverse image and direct image of $F$, but these are actually more general concepts and as such could perhaps cause confusion or unwanted connotations in some circumstances. The left-central-right terminology is very no-nonsense.

$^3$From the construction, it is evident that $F^*$ is precomposition with $F$ and hence, by definition of Kan extension, $F_!$ and $F_*$ are the left and right Kan extensions of $F$.

5

Proof. To see the implication from left to right: It is a standard fact of adjoint functors [nLa21a] that the left adjoint $F_!$ is fully faithful if and only if $\eta : \Gamma \to F^*F_!\Gamma$ is a natural isomorphism. If $F$ is fully faithful, then we can apply the co-Yoneda lemma:

$$(V \Rightarrow F^*F_!\Gamma) = (\exists V'.(FV \to FV') \times (V' \Rightarrow \Gamma)) \cong (\exists V'.(V \to V') \times (V' \Rightarrow \Gamma)) \cong (V \Rightarrow \Gamma)$$

i.e. $F^*F_!\Gamma \cong \Gamma$ and it is straightforward to see that this isomorphism is indeed the co-unit.

The implication from right to left is straightforward. By full faithfulness of $\mathbf{y}$ and by theorem 2.3.2 we have

$$(\mathbf{y}U \to \mathbf{y}V) \cong (U \to V),$$

$$(F_!\mathbf{y}U \to F_!\mathbf{y}V) \cong (\mathbf{y}FU \to \mathbf{y}FV) \cong (FU \to FV).$$

### 2.3.4 Dependent presheaf categories

Let $\mathcal{W}$ be a category. Then $\widehat{\mathcal{W}}$ is a category with families (CwF). The following notion is standard:

**Definition 2.3.5.** For any $\Gamma \in \widehat{\mathcal{W}}$, the **category of elements** of $\Gamma$, denoted

$$\int_{\mathcal{W}} \Gamma \quad \text{or} \quad \mathcal{W}/\Gamma \tag{5}$$

has objects $(W, \gamma)$ where $W \in \mathcal{W}$ and $\gamma : W \Rightarrow \Gamma$, and the morphisms $(W, \gamma) \to (W', \gamma')$ are the morphisms $\chi : W \to W'$ such that $\gamma' \circ \chi = \gamma$.

Clearly, we have an isomorphism $\mathcal{W}/U \cong \mathcal{W}/\mathbf{y}U$ between the slice category over $U$ and the category of elements of $\mathbf{y}U$.$^4$

We will use type-theoretic notation to make statements about the CwF $\widehat{\mathcal{W}}$, e.g. $\Gamma \vdash \text{Ctx}$ means $\Gamma \in \widehat{\mathcal{W}}$ and $\Gamma \vdash T$ type means $T \in \text{Ty}(\Gamma)$. Now for any context or closed type $\Gamma \in \widehat{\mathcal{W}}$, there is another CwF $\widehat{\mathcal{W}/\Gamma}$. Statements about this category will also be denoted using type-theoretic notation, but prefixed with '$\Gamma$ |'.

By unfolding the definitions of types and terms in a presheaf CwF, it is trivial to show that there is a correspondence — which we will treat as though it were the identity — between both CwFs:

- Contexts \(\Gamma \mid \Theta \vdash \mathrm{Ctx}\) correspond to types \(\Gamma \vdash \Theta\) type which we will think of as telescopes \(\Gamma.\Theta \vdash \mathrm{Ctx}\),
- Substitutions \(\Gamma \mid \sigma : \Theta \to \Theta'\) correspond to functions \(\Gamma \vdash \sigma : \Theta \to \Theta'\), or equivalently to telescope substitutions \(\mathrm{id}_{\Gamma}.\sigma : \Gamma.\Theta \to \Gamma.\Theta'\),
- Types \(\Gamma \mid \Theta \vdash T\) type correspond to types \(\Gamma.\Theta \vdash T\) type,
- Terms \(\Gamma \mid \Theta \vdash t : T\) correspond to terms \(\Gamma.\Theta \vdash t : T\).

In summary, the pipe is equivalent to a dot.

**Proposition 2.3.6.** We have an equivalence of categories $\widehat{\mathcal{W}/\Gamma} \simeq \widehat{\mathcal{W}}/\Gamma$.

Proof. $\to$ We map the presheaf $\Gamma \mid \Theta \vdash \text{Ctx}$ to the slice object $(\Gamma.\Theta, \pi)$.

$\leftarrow$ We map the slice object $(\Delta, \sigma)$ to the preimage of $\sigma$, i.e. the presheaf $\sigma^{-1}$ which sends $(W, \gamma)$ to $\{\delta : W \Rightarrow \Delta \mid \sigma \circ \delta = \gamma\}$.

$\widehat{\mathcal{W}/\Gamma}$ We need a natural isomorphism $\eta : \forall \Theta.(\Gamma \mid \eta : \Theta \cong \pi^{-1})$. If $\theta : (W, \gamma) \Rightarrow \Theta$, then we define $\eta(\theta) = (\gamma, \theta) : W \Rightarrow \Gamma.\Theta$ and indeed we have $\pi \circ (\gamma, \theta) = \gamma$. This is clearly invertible.

$^4$Depending on pedantic details, we may even have $\mathcal{W}/U = \mathcal{W}/\mathbf{y}U$.

6

$\widehat{\mathcal{W}}/\Gamma$ We need a natural isomorphism $\varepsilon : \forall(\Delta, \sigma).(\Gamma.\sigma^{-1}, \pi) \cong (\Delta, \sigma)$. Given $(\gamma, \delta) : W \Rightarrow \Gamma.\sigma^{-1}$ (i.e. we know $\sigma \circ \delta = \gamma$), we define $\varepsilon \circ (\gamma, \delta) = \delta : W \Rightarrow \Delta$. Then

$$\sigma \circ \varepsilon \circ (\gamma, \delta) = \sigma \circ \delta = \gamma = \pi \circ (\gamma, \delta), \tag{6}$$

so indeed we have a morphism in the slice category. It is inverted by sending $\delta : W \Rightarrow \Delta$ to $(\sigma \circ \delta, \delta) : W \Rightarrow \Gamma.\sigma^{-1}$. $\square$

**Corollary 2.3.7.** We have $\widehat{\mathcal{W}/U} \cong \widehat{\mathcal{W}/\mathbf{y}}U \simeq \widehat{\mathcal{W}}/\mathbf{y}U$. $\square$

### 2.3.5 Substitution and its adjoints

**Definition 2.3.8.** Given $U \in \mathcal{W}$, we write

- $\Sigma_U : \mathcal{W}/U \to \mathcal{W} : (W, \psi) \mapsto W$,
- $\Omega_U : \mathcal{W} \to \mathcal{W}/U : W \to (W \times U, \pi_2)$ (if $\mathcal{W}$ has cartesian products with $U$).

**Proposition 2.3.9.** If $\Omega_U$ exists, then $\Sigma_U \dashv \Omega_U$. We denote the unit as $\text{copy}_U : \text{Id} \to \Omega_U \Sigma_U$ and the co-unit as $\text{drop}_U : \Sigma_U \Omega_U \to \text{Id}$. $\square$

**Proposition 2.3.10.** 1. If $U \to \top$ is split epi, then the functor $\Omega_U$ is faithful.

2. (Not used). If $U \to \top$ is mono, then $\Sigma_U$ is full.$^5$

*Proof.* 1. We have some $v : \top \to U$, so that the action of $\Omega_U$ on morphisms sending $\varphi \mapsto \varphi \times U$ can be inverted: $\varphi = \pi_1 \circ (\varphi \times U) \circ (\text{id}, v)$.

2. Take slice objects $(W_1, \psi_1)$ and $(W_2, \psi_2)$ and a morphism $\varphi : W_1 \to W_2$. The fact that $U \to \top$ is mono just means that morphisms to $U$ are unique if existent. Then $\varphi$ is also a morphism between the slice objects. $\square$

**Definition 2.3.11.** Given $\chi : W'_0 \to W_0$ in $\mathcal{W}$, we write

- $\Sigma/\chi : \mathcal{W}/W'_0 \to \mathcal{W}/W_0 : (W', \psi') \mapsto (W', \chi \circ \psi')$,
- $\Omega/\chi : \mathcal{W}/W_0 \to \mathcal{W}/W'_0$ for the functor that maps $(W, \psi)$ to its pullback along $\chi$ (if $\mathcal{W}$ has pullbacks along $\chi$).

If $\chi = \pi_1 : W_0 \times U \to W_0$, we also write $\Sigma_U/\chi : \mathcal{W}/(W_0 \times U) \to \mathcal{W}/W_0$ and $\Omega_U/\chi : \mathcal{W}/W_0 \to \mathcal{W}/(W_0 \times U)$.

**Proposition 2.3.12.** If $\Omega/\chi$ exists, then $\Sigma/\chi \dashv \Omega/\chi$. We denote the unit as $\text{copy}/\chi : \text{Id} \to \Omega/\chi \Sigma/\chi$ and the co-unit as $\text{drop}/\chi : \Sigma/\chi \Omega/\chi \to \text{Id}$. $\square$

**Proposition 2.3.13** (Ultimately not used). 1. If $\chi$ is split epi, then $\Omega/\chi$ is faithful.

2. If $\chi$ is mono, then $\Sigma/\chi$ is full.$^6$

*Proof.* 1. We have some $v : W_0 \to W'_0$ such that $\chi \circ v = \text{id}$. Then the action of $\Omega/\chi$ on morphisms sending $\varphi \mapsto \varphi \times_{W_0} W'_0$ can be inverted: given $\varphi : (W_1, \psi_1) \to (W_2, \psi_2) \in \mathcal{W}/W_0$, we have

$$\varphi : W_1 \xrightarrow{(\text{id}, v \circ \psi_1)} W_1 \times_{W_0} W'_0 \xrightarrow{\varphi \times_{W_0} W'_0} W_2 \times_{W_0} W'_0 \xrightarrow{\pi_1} W_2. \tag{7}$$

2. Take a morphism $\varphi : (W_1, \chi \circ \psi_1) \to (W_2, \chi \circ \psi_2)$. Then $\chi \circ \psi_2 \circ \varphi = \chi \circ \psi_1$. Because $\chi$ is mono, this implies that $\psi_2 \circ \varphi = \psi_1$, i.e. $\varphi : (W_1, \psi_1) \to (W_2, \psi_2)$. $\square$

$^5$An earlier version asserted fullness of $\Omega_U$ instead, but proved the current theorem.
$^6$An earlier version asserted fullness of $\Omega/\chi$ instead, but proved the current theorem.

7

Definition 2.3.14. Given \(\sigma : \Psi' \to \Psi\) in \(\widehat{\mathcal{W}}\), we write

- \(\Sigma^{\prime \sigma}:\mathcal{W} / \Psi^{\prime}\to \mathcal{W} / \Psi :(W^{\prime},\psi^{\prime})\mapsto (W^{\prime},\sigma \circ \psi^{\prime}),\)
- \(\Omega^{\prime \sigma}:\mathcal{W} / \Psi \to \mathcal{W} / \Psi^{\prime}\) for the functor that maps \((W,\psi)\) to its pullback along \(\sigma\) (if \(\mathcal{W}\) has pullbacks along \(\sigma\)), by which we mean a universal solution \(W^{\prime}\) to the diagram

![img-2.jpeg](img-2.jpeg)

If \(\sigma = \pi_1: \Psi \times \Phi \to \Psi\), we also write \(\Sigma_{\Phi}^{\prime/\Psi}: \mathcal{W}/(\Psi \times \Phi) \to \mathcal{W}/\Psi\) and \(\Omega_{\Phi}^{\prime/\Psi}: \mathcal{W}/\Psi \to \mathcal{W}/(\Psi \times \Phi)\).

Proposition 2.3.15. If \(\Omega^{\prime \sigma}\) exists, then \(\Sigma^{\prime \sigma} \dashv \Omega^{\prime \sigma}\). We denote the unit as \(\mathrm{copy}^{\prime \sigma}: \mathrm{Id} \to \Omega^{\prime \sigma} \Sigma^{\prime \sigma}\) and the co-unit as \(\mathrm{drop}^{\prime \sigma}: \Sigma^{\prime \sigma} \Omega^{\prime \sigma} \to \mathrm{Id}\).

Proposition 2.3.16 (Not used). 1. If \(\sigma\) is surjective, then \(\Omega^{\prime \sigma}\) is faithful.

2. If  \( \sigma \)  is injective, then  \( \Sigma^{\prime\sigma} \)  is full. \( ^{7} \)

Proof. 1. If \(\sigma\) is surjective, then by the axiom of choice, there is at least a non-natural \(f: \Psi \to \Psi'\) such that \(\sigma \circ f = \mathrm{id}\). The rest of the proof is as for proposition 2.3.13.

2. Same as for proposition 2.3.13.

Definition 2.3.17. The functors \(\Sigma^{\prime \sigma} \dashv \Omega^{\prime \sigma}\) give rise to four adjoint functors

\[
\Sigma^ {\sigma |} \dashv \Omega^ {\sigma |} \dashv \Pi^ {\sigma |} \dashv \S^ {\sigma |} \tag {9}
\]

between  \( \widehat{W/\Psi} \)  and  \( \widehat{W/\Psi'} \) , of which the first three exist if only  \( \Sigma^{\prime\sigma} \)  exists. \( ^{8} \)

The units and co-units will be denoted:

\[
\begin{array}{l} \operatorname{copy} ^ {\sigma |}: \quad \operatorname{Id} \rightarrow \Omega^ {\sigma |} \Sigma^ {\sigma |} \\ \operatorname{const} ^ {\sigma |}: \quad \operatorname{Id} \rightarrow \Pi^ {\sigma |} \Omega^ {\sigma |} \\ \operatorname{reidx} ^ {\sigma |}: \quad \operatorname{Id} \rightarrow \S^ {\sigma |} \Pi^ {\sigma |} \\ \operatorname{drop} ^ {\sigma |}: \quad \Sigma^ {\sigma |} \Omega^ {\sigma |} \to \operatorname{Id} \\ \operatorname{app} ^ {\sigma |}: \quad \Omega^ {\sigma |} \Pi^ {\sigma |} \to \operatorname{Id} \\ \operatorname{unmerid} ^ {\sigma |}: \quad \Pi^ {\sigma |} \S^ {\sigma |} \to \operatorname{Id} \\ \end{array}
\]

We remark that, if we read presheaves over \(\mathcal{W}/\Psi\) as types in context \(\Psi\), then \(\Omega^{\sigma|}:\widehat{\mathcal{W}/\Psi}\to\widehat{\mathcal{W}/\Psi'}\) is the standard interpretation of substitution in a presheaf category. If \(\sigma=\pi:\Psi.A\to\Psi\) is a weakening morphism, then \(\Omega_{A}^{\Psi|}:=\Omega^{\pi|}\) is the weakening substitution, \(\Pi_{A}^{\Psi|}:=\Pi^{\pi|}:\widehat{\mathcal{W}/\Psi.A}\to\widehat{\mathcal{W}/\Psi}\) is isomorphic to the standard interpretation of the \(\Pi\)-type and \(\Sigma_{A}^{\Psi|}:=\Sigma^{\pi|}:\widehat{\mathcal{W}/\Psi.A}\to\widehat{\mathcal{W}/\Psi}\) is isomorphic to the standard interpretation of the \(\Sigma\)-type.

Theorem 2.3.18. Given types \(\Psi \vdash A, B\) type, the projections constitute a pullback diagram:

\[
\begin{array}{c} \Psi . (A \times B) \xrightarrow {\beta^ {\prime}} \Psi . A \\ \alpha^ {\prime} \Bigg \downarrow \quad \Bigg \downarrow \alpha \\ \Psi . B \xrightarrow {\beta} \Psi , \end{array} \tag {11}
\]

\( ^{7} \) An earlier version asserted fullness of  \( \Omega^{\prime\sigma} \)  instead, but proved the current theorem.

 \( ^{8} \) The latter functor is already a cartesian transpension functor; however we have not guaranteed its existence. Later on we will discuss a transpension functor for certain – not necessarily cartesian – shapes, modelled by multipliers, and there we will guarantee existence.

8

and every pullback diagram in a presheaf category is isomorphic to a diagram of this form. We have the following commutation properties:

|   | \( \Sigma_B \) | \( \Omega_B \) | \( \Pi_B \) | \( \S_B \)  |
| --- | --- | --- | --- | --- |
|  \( \Sigma_A \) | \( \Sigma^{\alpha}|\Sigma^{\beta'}| \cong \Sigma^{\beta}|\Sigma^{\alpha'}| \) | \( \Sigma^{\alpha'}|\Omega^{\beta'}| \cong \Omega^{\beta}|\Sigma^{\alpha}| \) | \( \Sigma^{\alpha}|\Pi^{\beta'}| \to \Pi^{\beta}|\Sigma^{\alpha'}| \) |   |
|  \( \Omega_A \) | \( \Omega^{\alpha}|\Sigma^{\beta}| \cong \Sigma^{\beta'}|\Omega^{\alpha'}| \) | \( \Omega^{\alpha'}|\Omega^{\beta}| = \Omega^{\beta'}|\Omega^{\alpha}| \) | \( \Omega^{\alpha}|\Pi^{\beta}| \cong \Pi^{\beta'}|\Omega^{\alpha'}| \) | \( \Omega^{\alpha'}|\S^{\beta}| \to \S^{\beta'}|\Omega^{\alpha}| \)  |
|  \( \Pi_A \) | \( \Pi^{\alpha}|\Sigma^{\beta'}| \leftarrow \Sigma^{\beta}|\Pi^{\alpha'}| \) | \( \Pi^{\alpha'}|\Omega^{\beta'}| \cong \Omega^{\beta}|\Pi^{\alpha}| \) | \( \Pi^{\alpha}|\Pi^{\beta'}| \cong \Pi^{\beta}|\Pi^{\alpha'}| \) | \( \Pi^{\alpha'}|\S^{\beta'}| \cong \S^{\beta}|\Pi^{\alpha}| \)  |
|  \( \S_A \) |  | \( \S^{\alpha'}|\Omega^{\beta}| \leftarrow \Omega^{\beta'}|\S^{\alpha}| \) | \( \S^{\alpha}|\Pi^{\beta}| \cong \Pi^{\beta'}|\S^{\alpha'}| \) | \( \S^{\alpha'}|\S^{\beta}| \cong \S^{\beta'}|\S^{\alpha}| \)  |

where every statement holds if the mentioned functors exist.

Proof. In the base category, it is evident that \(\Sigma^{\prime \alpha}\Sigma^{\prime \beta^{\prime}} = \Sigma^{\prime \beta}\Sigma^{\prime \alpha^{\prime}}\). By applying the functor \(\sqcup^{*}\), we obtain \(\Omega^{\alpha^{\prime}}|\Omega^{\beta}| = \Omega^{\beta^{\prime}}|\Omega^{\alpha}|\), whence by lemma 2.1.2 the entire diagonal of the commutation table.

It is a well-known fact that \(\Sigma\)- and \(\Pi\)-types are respected by substitution, which gives us the isomorphisms for swapping \(\Omega\) and either \(\Sigma\) or \(\Pi\). Lemma 2.1.2 then gives the rest.

Theorem 2.3.19. Given \(\sigma : \Psi' \to \Psi\), the following operations are invertible:

\[
\frac {\Psi \mid \Sigma^ {\sigma} | \Gamma \vdash T \text {type}}{\Psi^ {\prime} \mid \Gamma \vdash (\Omega^ {\sigma} | T) [ \mathsf {c o p y} ^ {\sigma} | ] \text {type}} \quad \frac {\Psi \mid \Sigma^ {\sigma} | \Gamma \vdash t : T}{\Psi^ {\prime} \mid \Gamma \vdash (\Omega^ {\sigma} | t) [ \mathsf {c o p y} ^ {\sigma} | ] : (\Omega^ {\sigma} | T) [ \mathsf {c o p y} ^ {\sigma} | ]} \tag {13}
\]

Proof. Note that \( T \) is a presheaf over \( (\mathcal{W} / \Psi) / \Sigma^{\sigma}|\Gamma \), and \( (\Omega^{\sigma}|T)[\mathrm{copy}^{\sigma}] \) is a presheaf over \( (\mathcal{W} / \Psi') / \Gamma \). We compare the objects of these categories:

\[
\operatorname{Obj} \left(\left(\mathcal {W} / \Psi\right) / \Sigma^ {\sigma} \mid \Gamma\right)
\]

\[
= (W \in \mathcal {W}) \times (\psi : W \Rightarrow \Psi) \times \exists ((W ^ {\prime}, \psi^ {\prime}) \in \mathcal {W} / \Psi^ {\prime}. (\chi : (W, \psi) \rightarrow \Sigma^ {\prime \sigma} (W ^ {\prime}, \psi^ {\prime})) \times ((W ^ {\prime}, \psi^ {\prime}) \Rightarrow \Gamma)
\]

\[
\cong (W \in \mathcal {W}) \times (\psi : W \Rightarrow \Psi) \times \exists W ^ {\prime}. (\psi^ {\prime}: W ^ {\prime} \Rightarrow \Psi^ {\prime}) \times (\chi : (W, \psi) \rightarrow \Sigma^ {\prime \sigma} (W ^ {\prime}, \psi^ {\prime})) \times ((W ^ {\prime}, \psi^ {\prime}) \Rightarrow \Gamma)
\]

\[
\cong (W \in \mathcal {W}) \times (\psi : W \Rightarrow \Psi) \times \exists W ^ {\prime}. (\psi^ {\prime}: W ^ {\prime} \Rightarrow \Psi^ {\prime}) \times (\chi : (W, \psi) \rightarrow (W ^ {\prime}, \sigma \circ \psi^ {\prime})) \times ((W ^ {\prime}, \psi^ {\prime}) \Rightarrow \Gamma)
\]

\[
\cong (W \in \mathcal {W}) \times \exists W ^ {\prime}. (\psi^ {\prime}: W ^ {\prime} \Rightarrow \Psi^ {\prime}) \times (\chi : W \rightarrow W ^ {\prime}) \times ((W ^ {\prime}, \psi^ {\prime}) \Rightarrow \Gamma)
\]

because \(\chi\) is a slice morphism iff \(\psi = \sigma \circ \psi' \circ \chi\)

\[
\cong (W \in \mathcal {W}) \times (\psi^ {\prime}: W \Rightarrow \Psi^ {\prime}) \times ((W, \psi^ {\prime}) \Rightarrow \Gamma)
\]

\[
\cong \operatorname{Obj} \left(\left(\mathcal {W} / \Psi^ {\prime}\right) / \Gamma\right).
\]

A similar consideration of the Hom-sets leads to the conclusion that both categories are isomorphic. Moreover, we remark that the isomorphism sends  \( ((W,\psi'),\gamma) \)  on the right to  \( ((W,\sigma\circ\psi'),\Sigma^{\sigma}|\gamma) \)  on the left. When we consider the action of  \( (\Omega^{\sigma}|T)[\mathsf{copy}^{\sigma}] \)  on  \( ((W,\psi'),\gamma) \) , we find:

\[
\left((W, \psi^ {\prime}) \triangleright (\Omega^ {\sigma} | T) [ \mathsf {c o p y} ^ {\sigma} | ] [ \gamma \rangle\right) = \left(\Sigma^ {\prime \sigma} (W, \psi^ {\prime}) \triangleright T \Big [ \Sigma^ {\sigma} | \gamma \Big \rangle\right)
\]

\[
= \left(\left(W, \sigma \circ \psi^ {\prime}\right) \triangleright T \left[ \Sigma^ {\sigma} | \gamma \right\rangle\right)
\]

In other words, the types \( T \) and \( (\Omega^{\sigma}|T)[\mathrm{copy}^{\sigma}] \) are equal over an isomorphism of categories. Then certainly \( T \) can be retrieved from \( (\Omega^{\sigma}|T)[\mathrm{copy}^{\sigma}] \). An identical argument works for terms.

#### 2.3.6 Reconstructing right adjoints

Proposition 2.3.20. Given a left adjoint functor \( L: \widehat{\mathcal{W}} \to \mathcal{C} \), we can construct a right adjoint \( R_L: \mathcal{C} \to \widehat{\mathcal{W}} \) without using the axiom of choice.

Proof. Define  \( (W \Rightarrow R_{L}\Gamma) := (L\mathbf{y}W \to \Gamma) \) . As a matter of notational hygiene, write  \( \alpha_{L} : (L\mathbf{y}W \to \Gamma) \to (W \Rightarrow R_{L}\Gamma) \)  for the identity function. Define restriction by  \( \alpha_{L}(\gamma) \circ \varphi = \alpha_{L}(\gamma \circ L\mathbf{y}\varphi) \)  and the functorial action by  \( R_{L}\sigma \circ \alpha_{L}(\gamma) = \alpha_{L}(\sigma \circ \gamma) \) . This is a well-defined presheaf functor.

Now we show that \( L \dashv R_L \). Since \( L \) is a left adjoint, it has a right adjoint \( R \). We have natural isomorphisms

\[
(W \Rightarrow R _ {L} \Gamma) = (L \mathbf {y} W \rightarrow \Gamma) \cong (\mathbf {y} W \rightarrow R \Gamma) \cong (W \Rightarrow R \Gamma)
\]

so that  \( R_{L} \)  is naturally isomorphic to R and indeed right adjoint to L.

□

9

## 3 Multipliers in the base category

### 3.1 Definition

**Definition 3.1.1.** Let $\mathcal{W}$ be a category with terminal object $\top$. An object $W$ is **pointable**$^{\S A}$ if $(\cdot): W \to \top$ is split epi. A category is **objectwise pointable**$^{\S A}$ if every object is pointable.

We have carefully chosen the above terminology to emphasize (1) that pointability is a property, not structure (the corresponding structure is called *pointed*), and (2) that objectwise pointability does *not* require that the pointings can be chosen naturally.

**Definition 3.1.2.** Let $\mathcal{W}$ be a category with terminal object $\top$. A **multiplier** for an object $U \in \mathcal{V}$ is a functor $\sqcup \ltimes U: \mathcal{W} \to \mathcal{V}$ such that $\top \ltimes U \cong U$.$^9$ This gives us a second projection $\pi_2: \forall W.W \ltimes U \to U$. We define the **fresh weakening functor** as $\exists_U: \mathcal{W} \to \mathcal{V}/U: W \mapsto (W \ltimes U, \pi_2)$, which is essentially the action of the multiplier on slice objects over $\top$.

We say that a multiplier is:

- **Endo** if it is an endofunctor (i.e. $\mathcal{V} = \mathcal{W}$), and in that case:

- **Copointed**$^{\S A}$ if there is also a first projection $\pi_1: \forall W.W \ltimes U \to W$,
- A **comonad**$^{\S A}$ if there is additionally a 'diagonal' natural transformation $\sqcup \ltimes \delta: \forall W.W \ltimes U \to (W \ltimes U) \ltimes U$ such that $\pi_1 \circ (W \ltimes \delta) = (\pi_1 \ltimes U) \circ (W \ltimes \delta) = \text{id}$.
- **Cartesian** if it satisfies the universal property of the cartesian product with $U$,

- $\top$-**slice faithful**$^{\S A}$ if $\exists_U$ is faithful, or equivalently (lemma 3.2.2) if $\sqcup \ltimes U$ is faithful,

- $\top$-**slice full**$^{\S A}$ if $\exists_U$ is full,

- $\top$-**slice objective pointable**$^{\S A}$ if $\pi_2: W \ltimes U \to U$ is always split epi, and in that case:

- $\top$-**slice shard-free**$^{\S A}$ if $\exists_U$ is essentially surjective on objects $(V, \psi)$ such that $\psi$ is split epi, i.e. if every such object in $\mathcal{V}/U$ is isomorphic to some $\exists_U W$.
- A split epi slice object $(V, \psi)$ that is not in the image of $\exists_U$ even up to isomorphism, will be called a **shard** of the multiplier.

- $\top$-**slice right adjoint**$^{\S A}$ if $\exists_U$ has a left adjoint $\exists_U: \mathcal{V}/U \to \mathcal{W}$.$^{10}$ We denote the unit as $\text{copy}_U: \text{Id} \to \exists_U \exists_U$ and the co-unit as $\text{drop}_U: \exists_U \exists_U \to \text{Id}$.

### 3.2 Basic properties

Some readers may prefer to first consult some examples (section 3.3).

**Proposition 3.2.1.** For any multiplier, we have $(\sqcup \ltimes U) = \Sigma_U \circ \exists_U$.

**Lemma 3.2.2.** The functor $\sqcup \ltimes U$ is faithful if and only if $\exists_U$ is faithful.

*Proof.* We have $(\sqcup \ltimes U) = \Sigma_U \circ \exists_U$ and $\Sigma_U: \mathcal{V}/U \to \mathcal{V}$ is faithful as is obvious from its definition.

**Proposition 3.2.3.** A multiplier with an objectwise pointable domain is $\top$-slice objectwise pointable.

*Proof.* The multiplier, as any functor, preserves split epimorphisms.

**Proposition 3.2.4.** Cartesian endomultipliers are comonads, and comonads are copointed.

**Proposition 3.2.5.** Cartesian endomultipliers are $\top$-slice right adjoint.

$^9$ $\sqcup \ltimes U$ is to be regarded as a single-character symbol, i.e. $\ltimes$ in itself is meaningless. In most concrete applications, however, the multiplier is defined as some monoidal product $\sqcup \otimes U$ with a given object $U$. For this reason, we also refrain from defining $U := \top \ltimes U$ because we may not have $\top \otimes U = U$ on the nose for the object of interest $U$.

$^{10}$ A functor $\sqcup \ltimes U$ with this property is usually called a *parametric* or *local right adjoint* [nLa21b], but the word 'local' is overloaded [nLa23a] and so is 'parametric', and we wanted uniform terminology.

10

Proof. The left adjoint to $\lrcorner_U = \Omega_U$ is then given by $\exists_U(V, \varphi) = \Sigma_U(V, \varphi) = V$ (proposition 2.3.9).

**Proposition 3.2.6.** Cartesian endomultipliers for pointable objects, are $\top$-slice faithful.

Pointability is not required however: cartesian endomultipliers for unpointable objects may be $\top$-slice faithful (examples 3.3.4 and 3.3.6).

Proof. In this case, $\lrcorner_U = \Omega_U$ and $U \to \top$ is split epi, so this is part of proposition 2.3.10.

Being $\top$-slice full expresses absence of diagonals in the following sense:

**Proposition 3.2.7.** If an endomultiplier for $U$ is both a comonad and $\top$-slice full, then $U$ is a terminal object. If the endomultiplier is moreover cartesian, then it is naturally isomorphic to the identity functor.

Proof. Consider the following diagram:

$$\top \ltimes U \xrightarrow{\top \ltimes \delta} (\top \ltimes U) \ltimes U \tag{14}$$

This is a morphism of slice objects $\top \ltimes \delta : \lrcorner_U \top \to \lrcorner_U(\top \ltimes U)$ and thus, by fullness of $\lrcorner_U$, of the form $\lrcorner_U v$ for some $v : \top \to \top \ltimes U$. This means in particular that

$$\mathrm{id}_{\top \ltimes U} = \pi_1 \circ (\top \ltimes \delta) = \pi_1 \circ (v \ltimes U) = v \circ \pi_1 : \top \ltimes U \to \top \ltimes U. \tag{15}$$

Composing on both sides with $\pi_2 : \top \ltimes U \cong U$, we find that $\mathrm{id}_U = (\pi_2 \circ v) \circ (\pi_1 \circ \pi_2^{-1})$ factors over $\top$, which means exactly that $\pi_2 \circ v : \top \to U$ and $\pi_1 \circ \pi_2^{-1} : U \to \top$ constitute an isomorphism, i.e. $U$ is terminal.

If $\sqcup \ltimes U$ is cartesian, then it is a cartesian product with a terminal object and therefore naturally isomorphic to the identity functor.

### 3.3 Examples

**Example 3.3.1 (Identity).** The identity functor $W \ltimes \top := W$ is an endomultiplier for $\top$.

It is cartesian, $\top$-slice fully faithful, $\top$-slice objectwise pointable iff $\mathcal{W}$ is objectwise pointable and in that case $\top$-slice shard-free, and $\top$-slice right adjoint.

The functor $\lrcorner_\top : \mathcal{W} \to \mathcal{W}/\top : W \mapsto (W, (\,))$ has a left adjoint $\exists_\top : \mathcal{W}/\top \to \mathcal{W} : (W, (\,)) \mapsto W$.

**Example 3.3.2 (Cartesian product).** Let $\mathcal{W}$ be a category with finite products and $U \in \mathcal{W}$.

Then $\sqcup \times U$ is an endomultiplier for $U$.

It is cartesian, $\top$-slice faithful if (but not only if) $U$ is pointable (proposition 3.2.6), $\top$-slice full if and only if $U \cong \top$ (proposition 3.2.7) and $\top$-slice right adjoint (proposition 3.2.5). We do not consider $\top$-slice objectwise pointability for this general case.

The functor $\lrcorner_U = \Omega_U : V \mapsto (V \times U, \pi_2)$ has a left adjoint $\exists_U = \Sigma_U : (W, \psi) \mapsto W$. Hence, we have $\exists_U \lrcorner_U = \sqcup \times U$.

**Example 3.3.3 (Affine cubes).** Let $\square^k$ be the category of affine non-symmetric $k$-ary cubes $\mathbb{I}^n$ as used in [BCH14] (binary) or [BCM15] (unary). A morphism $\varphi : \mathbb{I}^m \to \mathbb{I}^n$ is a function $\sqcup \langle \varphi \rangle : \{i_1, \dots, i_n\} \to \{i_1 \dots i_m, 0, \dots, k-1\}$ such that $i \langle \varphi \rangle = j \langle \varphi \rangle \notin \{0, \dots, k-1\}$ implies $i = j$. We also write $\varphi = (i_1 \langle \varphi \rangle / i_1, \dots, i_n \langle \varphi \rangle / i_n)$. This category is objectwise pointable if and only if $k > 0$.

Consider the functor $\sqcup * \mathbb{I} : \square^k \to \square^k : \mathbb{I}^n \mapsto \mathbb{I}^{n+1}$, which is a multiplier for $\mathbb{I}$. It acts on morphisms $\varphi : \mathbb{I}^m \to \mathbb{I}^n$ by setting $\varphi * \mathbb{I} = (\varphi, i_{m+1} / i_{n+1})$.

It is straightforwardly seen to be copointed, not a comonad, $\top$-slice fully faithful, $\top$-slice objectwise pointable iff $k \neq 0$ and in that case $\top$-slice shard-free, and $\top$-slice right adjoint.

The functor $\lrcorner_\mathbb{I} : \mathbb{I}^n \mapsto (\mathbb{I}^{n+1}, (i_{n+1} / i_1))$ has as left adjoint the functor $\exists_\mathbb{I}$ which sends $(\mathbb{I}^n, \psi)$ to $\mathbb{I}^n$ if $i_1 \langle \psi \rangle \in \{0, \dots, k-1\}$ and to $\mathbb{I}^{n-1}$ (by removing the variable $i_1 \langle \psi \rangle$ and renaming the next ones) otherwise. The action on morphisms is straightforwardly constructed.

11

In the case where $k = 2$, we can throw in an involution $\neg : \mathbb{I} \to \mathbb{I}$. This changes none of the above results, except that $i_1 \langle \psi \rangle$ may be the negation $\neg j$ of a variable $j$, in which case $\exists_U$ removes the variable $j$.

**Example 3.3.4** (Cartesian cubes). Let $\boxtimes^k$ be the category of cartesian non-symmetric $k$-ary cubes $\mathbb{I}^n$. A morphism $\varphi : \mathbb{I}^m \to \mathbb{I}^n$ is any function $\sqcup \langle \varphi \rangle : \{i_1, \dots, i_n\} \to \{i_1 \dots i_m, 0, \dots, k-1\}$. This category is objectwise pointable if and only if $k > 0$.

Consider the functor $\sqcup \times \mathbb{I} : \boxtimes^k \to \boxtimes^k : \mathbb{I}^n \mapsto \mathbb{I}^{n+1}$, which is an endomultiplier for $\mathbb{I}$.

It is cartesian (hence $\top$-slice non-full and right adjoint with $\exists_{\mathbb{I}}(W, \psi) = W$), $\top$-slice full, $\top$-slice objectwise pointable iff $k > 0$ and in that case $\top$-slice shard-free.

Again, involutions change none of the above results.

**Example 3.3.5** (CCHM cubes). Let $\boxtimes_{\vee, \wedge, \neg}$ be the category of (binary) CCHM cubes [CCHM17]. What's special here is that we have connections $\vee, \wedge : \mathbb{I}^2 \to \mathbb{I}$ (as well as involutions). This category is objectwise pointable.

Again, we consider the functor $\sqcup \times \mathbb{I} : \boxtimes_{\vee, \wedge, \neg} \to \boxtimes_{\vee, \wedge, \neg} : \mathbb{I}^n \mapsto \mathbb{I}^{n+1}$, which is an endomultiplier for $\mathbb{I}$.

It is cartesian (hence $\top$-slice non-full and right adjoint with $\exists_{\mathbb{I}}(W, \psi) = W$), $\top$-slice faithful and $\top$-slice objectwise pointable but not shard-free (since $(\mathbb{I}^2, \vee)$ and $(\mathbb{I}^2, \wedge)$ are shards).

**Example 3.3.6** (Clocks). Let $\odot$ be the category of clocks, used as a base category in guarded type theory [BM20]. Its objects take the form $(i_1 : \odot_{k_1}, \dots, i_n : \odot_{k_n})$ where all $k_j \ge 0$. We can think of a variable of type $\odot_k$ as representing a clock (i.e. a time dimension) paired up with a certificate that we do not care what happens after the time on this clock exceeds $k$. Correspondingly, we have a map $\odot_k \to \odot_\ell$ if $k \le \ell$. These maps, together with weakening, exchange, and contraction, generate the category. The terminal object is $(\cdot)$ and every other object is unpointable.

Consider in this category the functor $\sqcup \times (i : \odot_k) : \odot \to \odot : W \mapsto (W, i : \odot_k)$, which is an endomultiplier for $(i : \odot_k)$.

It is cartesian (hence $\top$-slice non-full and right adjoint with $\exists_{(i: \odot_k)}(W, \psi) = W$), $\top$-slice faithful and not $\top$-slice objectwise pointable.

**Example 3.3.7** (Twisting posets). Let $\mathcal{P}$ be the category of finite non-empty posets and monotonic maps. This category is objectwise pointable.

Let $\mathbb{I} = \{0 < 1\}$ and let $W \ltimes \mathbb{I} = (W^{\mathrm{op}} \times \{0\}) \cup (W \times \{1\})$ with $(x, 0) < (y, 1)$ for all $x, y \in W$. This is an endomultiplier for $\mathbb{I}$.

It is easily seen to be: not copointed, $\top$-slice faithful but not full, $\top$-slice objectwise pointable but not shard-free, and $\top$-slice right adjoint.

The functor $\exists_{\mathbb{I}} : V \mapsto (V \ltimes \mathbb{I}, \pi_2)$ has a left adjoint $\exists_{\mathbb{I}} : (W, \psi) \mapsto \psi^{-1}(0)^{\mathrm{op}} \uplus \psi^{-1}(1)$ where elements from different sides of the $\uplus$ are incomparable.

We see this category as a candidate base category for directed type theory. The idea is that a cell over $W$ is a commutative diagram in a category. A problem here is that a cell over a discrete poset such as $\{x, y\}$ where $x$ and $y$ are incomparable, should then be the same as a pair of cells over $\{x\}$ and $\{y\}$. This will require that we restrict from presheaves to sheaves, but that makes it notoriously difficult to model the universe [XE16]. One solution would be to restrict to totally ordered sets, but then we lose the left adjoint $\exists_{\mathbb{I}}$. We address this in example 3.3.8.

**Example 3.3.8** (Twisted cubes). Let $\boxtimes$ be the subcategory of $\mathcal{P}$ whose objects are generated by $\top$ and $\sqcup \ltimes \mathbb{I}$ (note that every object then also has an opposite since $\top^{\mathrm{op}} = \top$ and $(V \ltimes \mathbb{I})^{\mathrm{op}} \cong V \ltimes \mathbb{I}$), and whose morphisms are given by

- $(\varphi, 0) : \boxtimes(V, W \ltimes \mathbb{I})$ if $\varphi : \boxtimes(V, W^{\mathrm{op}})$,
- $(\varphi, 1) : \boxtimes(V, W \ltimes \mathbb{I})$ if $\varphi : \boxtimes(V, W)$,
- $\varphi \ltimes \mathbb{I} : \boxtimes(V \ltimes \mathbb{I}, W \ltimes \mathbb{I})$ if $\varphi : \boxtimes(V, W)$,
- $(\cdot) : \boxtimes(V, \top)$.

12

Note that this collection automatically contains all identities, composites, and opposites. It is isomorphic to Pinyo and Kraus's category of twisted cubes, as can be seen from the ternary representation of said category [PK20, def. 34]. This category is objectwise pointable.

Again, we consider the functor $\sqcup \ltimes \mathbb{I} : \mathbb{M} \to \mathbb{M}$, which is well-defined by construction of $\mathbb{M}$ and an endomultiplier for $\mathbb{I}$. It corresponds to Pinyo and Kraus's twisted prism functor.

It is: not copointed and $\top$-slice fully faithful, objectwise pointable, shard-free and right adjoint.

The left adjoint to $\exists_1 : W \mapsto (W \ltimes \mathbb{I}, \pi_2)$ is now given by

$$\exists_1 : \left\{ \begin{array}{l l} (W, ((), 0)) & \mapsto W^{\mathrm{op}} \\ (W, ((), 1)) & \mapsto W \\ (W \ltimes \mathbb{I}, () \ltimes \mathbb{I}) & \mapsto W, \end{array} \right. \tag{16}$$

with the obvious action on morphisms.

Example 3.3.9 (Embargoes). In order to define contextual fibrancy [BT21] internally, we need to be able to somehow put a sign in the context $\Gamma \mathbf{\Omega} \Theta$ in order to be able to say: the type is fibrant over $\Theta$ in context $\Gamma$. We call this an embargo and say that $\Theta$ is embargoed whereas $\Gamma$ is not. If $\mathcal{C}$ is the category of contexts, then $\Gamma \mathbf{\Omega} \Theta$ can be seen as an object of the arrow category $\mathcal{C}^\uparrow$, namely the arrow $\Gamma \Theta \to \Gamma$.

If $\mathcal{C} = \widehat{\mathcal{W}}$ happens to be a presheaf category, then we have an isomorphism of categories $H : \widehat{\mathcal{W}}^\uparrow \cong \widehat{\mathcal{W} \times \uparrow}$ where $\uparrow = \{\bot \to \top\}$. Under this isomorphism, we have $\mathbf{y}(W, \top) \cong H(\mathbf{y}W \xrightarrow{\mathrm{id}} \mathbf{y}W)$ which we think of as $\mathbf{y}W \mathbf{\Omega} \top$ and $\mathbf{y}(W, \bot) \cong H(\bot \xrightarrow{\mathrm{id}} \mathbf{y}W)$ which we think of as $\mathbf{y}W \mathbf{\Omega} \bot \bot$. Thus, forgetting the second component of $(W, o)$ amounts to forgetting the embargoed part of the context. A $(W, \top)$-cell of $\Gamma \mathbf{\Omega} \Theta$ is a $W$-cell of $\Gamma \Theta$, i.e. a partly embargoed $W$-cell. We can extract the unembargoed information by restricting to $(W, \bot)$, as a $(W, \bot)$-cell of $\Gamma \mathbf{\Omega} \Theta$ is just a $W$-cell of $\Gamma$.

There are 3 adjoint functors $\bot \dashv () \dashv \top$ between $\uparrow$ and Point from which we obtain 3 adjoint functors $(\mathrm{Id}, \bot) \dashv \pi_1 \dashv (\mathrm{Id}, \top)$ between $\mathcal{W} \times \uparrow$ and $\mathcal{W}$. The rightmost functor $(\mathrm{Id}, \top) : \mathcal{W} \to \mathcal{W} \times \uparrow$ is a multiplier for the terminal object $\mathbf{\Omega} \colon := (\top, \top) \in \mathcal{W} \times \uparrow$, denoted $\sqcup \ltimes \mathbf{\Omega}$.

It is: not endo, $\top$-slice fully faithful, $\top$-slice objectwise pointable iff $\mathcal{W}$ is and in that case $\top$-slice shard-free, and $\top$-slice right adjoint.

In order to look at the left adjoint, note first that since $\mathbf{\Omega}$ is terminal, we have $(\mathcal{W} \times \uparrow)/\mathbf{\Omega} \cong \mathcal{W} \times \uparrow$ and clearly $\exists_1$ corresponds to $(\mathrm{Id}, \top)$ under this isomorphism. This functor is part of a chain of three adjoint functors $(\mathrm{Id}, \bot) \dashv \pi_1 \dashv (\mathrm{Id}, \top)$ so that the multiplier is not just $\top$-slice right adjoint but $\exists_1$ even has a further left adjoint!

If $\sqcup \ltimes U : \mathcal{V} \to \mathcal{W}$ is a multiplier, then we can lift it to a multiplier $\sqcup \ltimes (U \ltimes \mathbf{\Omega}) : \mathcal{V} \times \uparrow \to \mathcal{W} \times \uparrow$ by applying it to the first component, i.e. $(W, o) \ltimes (U \ltimes \mathbf{\Omega}) = (W \ltimes U, o)$. The resulting multiplier inherits all properties in definition 3.1.2 from $\sqcup \ltimes U$, except that it is never $\top$-slice objectwise pointable.

Example 3.3.10 (Enhanced embargoes). If $\sqcup \ltimes U$ is a copointed endomultiplier on $\mathcal{W}$, then we might want to apply it to an arrow $V \xrightarrow{\psi} W$ by sending it to $V \ltimes U \xrightarrow{\psi \circ \pi_1} W$. This operation is not definable on $\mathcal{W} \times \uparrow$, which only encodes arrows of the forms $W \to W$ (as $(W, \top)$) and $\bot \to W$ (as $(W, \bot)$). For this reason, we move to the comma category $\mathcal{W}_\mathbf{\Omega} := \mathcal{W}_\bot / \mathcal{W}$ where $\mathcal{W}_\bot$ is $\mathcal{W}$ with a freely added initial object. This comma category has as its objects arrows $V \xrightarrow{\psi} W$ where $V \in \mathcal{W}_\bot$ and $W \in \mathcal{W}$. Morphisms are simply commutative squares. A $(V \xrightarrow{\psi} W)$-cell is now a non-embargoed $W$-cell $\gamma$ with embargoed information about $\gamma \circ \psi$.

We still have three adjoint functors $(\bot \xrightarrow{\mathrm{id}} \sqcup) \dashv \mathrm{Cod} \dashv \Delta$ where $\Delta W = (W \xrightarrow{\mathrm{id}} W)$. Further right adjoints would be $\mathrm{Dom} \dashv (\sqcup \xrightarrow{\mathrm{id}} \top)$, but $\mathrm{Dom}$ is not definable as the domain might be $\bot$. We take $\Delta$ as a multiplier for $\mathbf{\Omega} \colon := (\top \to \top)$, denoted $\sqcup \ltimes \mathbf{\Omega} \colon := \Delta$.

The multiplier $\sqcup \ltimes \mathbf{\Omega}$ is: not endo, $\top$-slice fully faithful, $\top$-slice objectwise pointable iff $\mathcal{W}$ is objectwise pointable and in that case generally not $\top$-slice shard-free (as every non-identity arrow is a shard), and $\top$-slice right adjoint.

Now we can still lift any multiplier $\sqcup \ltimes U : \mathcal{V} \to \mathcal{W}$ to a multiplier $\sqcup \ltimes (U \ltimes \mathbf{\Omega}) : \mathcal{V}_\mathbf{\Omega} \to \mathcal{W}_\mathbf{\Omega}$ for $(U \ltimes \mathbf{\Omega}) = (U \xrightarrow{\mathrm{id}} U)$ by applying it to both domain and codomain, i.e. $(V \xrightarrow{\psi} W) \ltimes (U \ltimes \mathbf{\Omega}) :=$

13

$$(V \ltimes U \xrightarrow{\psi \ltimes U} W \ltimes U)$$, where by convention $$\bot \ltimes U = \bot$$. It inherits all properties in definition 3.1.2 from $$\sqcup \ltimes U$$, except that it is never $$\top$$-slice objectwise pointable.

For reasons that will become apparent later, we write $$\mathbf{!}\sqrt{\sqcup} := (\sqcup \to \top)$$. Note that a $$(\mathbf{!}\sqrt{U})$$-cell is an unembargoed point with embargoed information about the degenerate $$U$$-cell on that point. E.g. in a context $$\Gamma.\mathbf{!}\Theta$$, an $$(\mathbf{!}\sqrt{\mathbb{I}})$$-cell is exactly a path in $$\Theta$$ above a point in $$\Gamma$$, which is a concept that we need to quantify over when defining internal Kan fibrancy [BT21].

If $$\sqcup \ltimes U$$ is copointed, then we can also lift a multiplier for $$U$$ to a multiplier for $$(\mathbf{!}\sqrt{U})$$ by applying the original one only to the domain, i.e. $$(V \xrightarrow{\psi} W) \ltimes (\mathbf{!}\sqrt{U}) = (V \ltimes U \xrightarrow{\psi \circ \pi_1} W)$$. This again inherits all properties in definition 3.1.2 from $$\sqcup \ltimes U$$, except that it is never $$\top$$-slice objectwise pointable, and that $$\top$$-slice fullness requires that $$\pi_1 : \sqcup \ltimes U \to \text{Id}$$ is objectwise epi (e.g. because $$U$$ is pointable) and $$\sqcup \ltimes U$$ is slicewise full, and that $$\top$$-slice right adjointness can only be inherited if $$\mathcal{W}$$ has pushouts. In that case, we have

$$\exists_{(\mathbf{!}\sqrt{U})}(W_1 \xrightarrow{\psi} W_2, (\psi_1, ())) = (\exists_U(W_1, \psi 1) \to W_2 \uplus_{W_1} \exists_U(W_1, \psi 1)). \tag{17}$$

Here, the morphism $$W_1 = \Sigma_U(W_1, \psi_1) \to \exists_U(W_1, \psi 1)$$ is an instance of the natural transformation $$\text{hide}_U : \Sigma_U \to \exists_U$$ obtained by lemma 2.1.1 from $$\pi_1 : \sqcup \ltimes U = \Sigma_U \upharpoonright_U \to \text{Id}$$ (theorem 3.4.4). Indeed, given a morphism of slice objects $$(\chi_1, \chi_2) : (W_1 \xrightarrow{\psi} W_2, (\psi_1, ())) \to \upharpoonright_{(\mathbf{!}\sqrt{U})}(V_1 \xrightarrow{\varphi} V_2)$$, i.e.

![img-3.jpeg](img-3.jpeg)

we get a commutative diagram (the upper right square commutes by construction of $$\text{hide}_U$$)

![img-4.jpeg](img-4.jpeg)

so the top horizontal line, which is the transpose of $$\chi_1$$, is a well-typed first component of the transpose of $$(\chi_1, \chi_2)$$, while the three horizontal lines together constitute an arrow from the pushout to $$V_2$$ which is a well-typed second component. Conversely, given $$(\omega_1, \omega_2) : \exists_{(\mathbf{!}\sqrt{U})}(W_1 \xrightarrow{\psi} W_2, (\psi_1, ())) \to (V_1 \xrightarrow{\varphi} V_2)$$, i.e. (unwrapping the pushout)

![img-5.jpeg](img-5.jpeg)

14

we can take the transpose of $\omega_1$ as a first component and $\chi_2$ as a second component of the transpose of $(\omega_1, \omega_2)$. It remains to show that these form a commutative diagram with $\psi : W_1 \to W_2$ and $\varphi \circ \pi_1 : V_1 \ltimes U \to V_2$. But we have a commutative diagram

$$\begin{array}{c} W_1 \xlongequal{\quad} \Sigma_U(W_1, \psi_1) \xrightarrow{\quad \Sigma_U \text{copy}_U \quad} \Sigma_U \lrcorner \\ \Bigg\downarrow \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\pi_1} \\ \exists_U(W_1, \psi_1) \xrightarrow{\quad \exists_U \text{copy}_U \quad} \exists_U \lrcorner \\ \Bigg\downarrow \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\text{hide}_U} \quad \Bigg\downarrow_{\pi_1} \\ W_1 \xrightarrow{\quad \text{hide}_U \quad} \exists_U(W_1, \psi_1) \xrightarrow{\quad \omega_1 \quad} \quad V_1 \end{array}$$

which can be pasted on top of the previous one to settle the matter. Finally, it is surprisingly easy to verify that the transposition operations just defined are mutually inverse.

**Example 3.3.11** (Depth $d$ cubes). Let $\square_d$ with $d \geq -1$ be the category of depth $d$ cubes, used as a base category in degrees of relatedness [ND18, Nuy18].$^{11}$ Its objects take the form $(i_1 : (\lrcorner k_1), \dots, i_n : (\lrcorner k_n))$ where all $k_j \in \{0, \dots, d\}$. Conceptually, we have a map $(\lrcorner k) \to (\lrcorner \ell)$ if $k \geq \ell$. Thus, morphisms $\varphi : (i_1 : (\lrcorner k_1), \dots, i_n : (\lrcorner k_n)) \to (j_1 : (\lrcorner \ell_1), \dots, j_m : (\lrcorner \ell_m))$ send every variable $j : (\lrcorner \ell)$ of the codomain to a value $j \langle \varphi \rangle$, which is either 0, 1 or a variable $i : (\lrcorner k)$ of the domain such that $k \geq \ell$. The terminal object is () and the category is objectwise pointable.

Consider in this category the functor $\sqcup \times (i : (\lrcorner k)) : \square_d \to \square_d : W \mapsto (W, i : (\lrcorner k))$, which is an endomultiplier for $(i : (\lrcorner k))$.

It is cartesian (hence $\top$-slice non-full and right adjoint with $\exists_{(i: (\lrcorner k))(W, \psi)} = W$), $\top$-slice faithful, objectwise pointable and shard-free.

**Example 3.3.12** (Erasure). Let $\text{Erase}_d = \{\top \leftarrow 0 \leftarrow 1 \leftarrow \dots \leftarrow d\}$ with $d \geq -1$. This category has cartesian products $m \times n = \max(m, n)$ and only the terminal object is pointable. We remark that $\widetilde{\text{Erase}}_0$ is the Sierpiński topos.

We consider the endomultiplier $\sqcup \times i : \text{Erase}_d \to \text{Erase}_d$.

It is cartesian (hence $\top$-slice non-full and right adjoint with $\exists_i(j, \psi) = j$), $\top$-slice faithful and not $\top$-slice objectwise pointable.

We believe that this base category is a good foundation for studying the semantics of erasure of irrelevant subterms in Degrees of Relatedness [ND18]. The idea is that, for a presheaf $\Gamma$, the set $\top \Rightarrow \Gamma$ is the set of elements, whereas the set $i \Rightarrow \Gamma$ is the set of elements considered up to $i$-relatedness, but also whose existence is only guaranteed by a derivation up to $i$-relatedness.

**Example 3.3.13** (Counterexample for $\top$-slice faithful). Let $\square_\perp^2$ be the category of binary cartesian cubes extended with an initial object. We consider the cartesian product $\sqcup \times \perp$ which sends everything to $\perp$. This is not $\top$-slice faithful, as $\lrcorner \perp$ sends both $(0/i)$ and $(1/i) : () \to (i : \mathbb{I})$ to $[] : (\perp, []) \to (\perp, [])$. It is not $\top$-slice full, as there is no $\psi : () \to \perp$ such that $\psi \times \perp = [] : \lrcorner \perp() \to \lrcorner \perp\perp$.

## 3.4 Properties

### 3.4.1 Functoriality

**Definition 3.4.1.** A multiplier morphism or morphism multiplier for $\upsilon : U \to U'$ is a natural transformation $\sqcup \ltimes \upsilon : \sqcup \ltimes U \to \sqcup \ltimes U'$ such that $\pi_2 \circ (\top \ltimes \upsilon) \circ \pi_2^{-1} = \upsilon : U \to U'$ (or equivalently $\pi_2 \circ (W \ltimes \upsilon) = \upsilon \circ \pi_2 : W \ltimes U \to U'$ for all $W$).

- If both multipliers are copointed, then $\upsilon$ is said to be a morphism of copointed multipliers$^{1A}$ if it is a morphism of copointed endofunctors, i.e. if $\pi_1 \circ (W \ltimes \upsilon) = \pi_1$,

$^{11}$For $d = -1$, we get the point category. For $d = 0$, we get the category of binary cartesian cubes $\square^2$. For $d = 1$, we get the category of bridge/path cubes [NVD17, Nuy18].

15

- If both multipliers are comonads, then $v$ is said to be a **comonad morphism of multipliers**$^{\S A}$ if it is a comonad morphism, i.e. if additionally $(W \ltimes \delta) \circ (W \ltimes v) = ((W \ltimes v) \ltimes v) \circ (W \ltimes \delta)$,
- A morphism of cartesian multipliers is **cartesian** if it is the cartesian product with $v$.

**Proposition 3.4.2.** A morphism of copointed multipliers, whose domain and codomain happen to be cartesian multipliers, is cartesian.

*Proof.* We have $\pi_2 \circ (W \ltimes v) = v \circ \pi_2$ and $\pi_1 \circ (W \ltimes v) = \pi_1$. Hence, $(W \ltimes v) = (\pi_1, v \circ \pi_2) = W \ltimes v$. $\square$

**Proposition 3.4.3** (Functoriality). A multiplier morphism $\sqcup \ltimes v : \sqcup \ltimes U \to \sqcup \ltimes U'$ gives rise to a natural transformation $\Sigma'^v \circ \bot_U \to \bot_{U'}$. Hence, for $\top$-slice right adjoint multipliers, we also have $\exists_{U'} \circ \Sigma'^v \to \exists_U$.

*Proof.* We have to show that for every $W \in \mathcal{W}$, we get $(W \ltimes U, v \circ \pi_2) \to (W \ltimes U', \pi_2)$. The morphism $W \ltimes v : W \ltimes U \to W \ltimes U'$ does the job. The second statement follows from lemma 2.1.1. $\square$

### 3.4.2 Quantification and quotient theorem

**Theorem 3.4.4** ($\top$-slice quantification theorem). If $\sqcup \ltimes U$ is

1. $\top$-slice fully faithful and right adjoint, then we have a natural isomorphism $\mathsf{drop}_U : \exists_U \bot_U \cong \mathsf{Id}$.
2. copointed, then we have:

(a) \(\mathsf{hide}_U:\Sigma_U\to \exists_U\) (if T-slice right adjoint),
(b) \(\mathsf{soil}_U:\perp_U\to \Omega_U\) (if \(\Omega_U\) exists),
(c) in any case \(\Sigma_U\perp_U\to \mathrm{Id}\)

3. a comonad, then there is a natural transformation \(\Sigma^{\prime \delta}\circ \bot_U\to \bot_{U\times U}\), where we compose multipliers as in theorem 3.6.1.
4. cartesian, then we have:

(a) \(\exists_U\cong \Sigma_U\)
(b) \(\perp_U\cong \Omega_U\)
(c) \(\exists_U\perp_U\cong \Sigma_U\Omega_U = (\sqcup \ltimes U)\cong (\sqcup \ltimes U).\)

Moreover, these isomorphisms become equalities by choosing $\exists_U$ and $\Omega_U$ wisely (both are defined only up to isomorphism).

*Proof.* 1. This is a standard fact of fully faithful right adjoints such as $\bot_U$.

2. By lemma 2.1.1, it is sufficient to prove \(\Sigma_U \perp_U \to \operatorname{Id}\). But \(\Sigma_U \perp_U = (\sqcup \ltimes U)\), so this is exactly the statement that the multiplier is copointed.
3. This is a special case of proposition 3.4.3.
4. By uniqueness of the cartesian product, we have \(\perp_U \cong \Omega_U\). Then the multiplier is \(\top\)-slice right adjoint with \(\exists_U \cong \Sigma_U\). The last point is now trivial.

**Theorem 3.4.5** ($\top$-slice quotient theorem$^{\S A}$ for $\top$-slice objectwise pointable multipliers). If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice objectwise pointable, fully faithful and shard-free, then $\bot_U : \mathcal{W} \simeq \mathcal{V} // U$ is an equivalence of categories, where $\mathcal{V} // U$ is the full subcategory of $\mathcal{V} / U$ whose objects are the split epimorphic slice objects.

*Proof.* By $\top$-slice objectwise pointability, $\bot_U$ lands in $\mathcal{V} // U$. The other properties assert that $\bot_U$ is fully faithful and essentially surjective as a functor $\mathcal{W} \to \mathcal{V} // U$. $\square$

16

This quotient theorem applies to examples 3.3.1, 3.3.3, 3.3.8 and 3.3.9. However, we can extend the quotient theorem to also consider multipliers that are not $\top$-slice objectwise pointable theorem 3.4.10, and then it will apply to more examples.

We will use the quotient theorem in theorem 4.4.7 on transpension elimination, a dependent eliminator for the transpension type from which we can build a dependent eliminator for BCM's $\Psi$-type and prove BCM's $\Phi$-rule [Mou16, BCM15].

### 3.4.3 Dealing with unpointability

Since multipliers that are not $\top$-slice objectwise pointable, do not guarantee that $\nexists_U$ produces split epi slice objects, we need to come up with a larger class of suitable epi-like morphisms to $U$ before we can proceed.

**Definition 3.4.6.** Given a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$, we say that a morphism $\varphi : V \to U$ is **dimensionally split** if there is some $W \in \mathcal{W}$ such that $\pi_2 : W \ltimes U \to U$ factors over $\varphi$. The other factor $\chi$ such that $\pi_2 = \varphi \circ \chi$ will be called a **dimensional section** of $\varphi$. We write $\mathcal{V} // U$ for the full subcategory of $\mathcal{V} / U$ of dimensionally split slice objects.

The $\top$-slice objectwise pointability condition for multipliers is automatically satisfied if we replace 'split epi' with 'dimensionally split':

**Corollary 3.4.7.** For any multiplier $\sqcup \ltimes U$, any projection $\pi_2 : W \ltimes U \to U$ is dimensionally split. $\square$

**Proposition 3.4.8.** Take a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$.

1. If $\varphi \circ \chi$ is dimensionally split, then so is $\varphi$.
2. The identity morphism $\text{id}_U : U \to U$ is dimensionally split.
3. If $\varphi : V \to U$ is dimensionally split and $\chi : V' \to V$ is split epi, then $\varphi \circ \chi : V' \to U$ is dimensionally split.
4. Every split epimorphism to $U$ is dimensionally split.
5. If $\sqcup \ltimes U$ is $\top$-slice objectwise pointable, then every dimensionally split morphism is split epi.

*Proof.* 1. If $\pi_2 : W \ltimes U \to U$ factors over $\varphi \circ \chi$, then it certainly factors over $\varphi$.

2. Since $\pi_2 : \top \ltimes U \to U$ factors over $\text{id}_U$.
3. Let $\varphi'$ be a dimensional section of $\varphi$ and $\chi'$ a section of $\chi$. Then $\chi' \circ \varphi'$ is a dimensional section of $\varphi \circ \chi$.
4. From the previous two points, or (essentially by composition of the above reasoning) because if $\chi : U \to V$ is a section of $\varphi : V \to U$, then $\chi \circ \pi_2 : \top \ltimes U \to V$ is a dimensional section of $\varphi$.
5. If $\varphi : V \to U$ is dimensionally split, then some $\pi_2 : W \ltimes U \to U$ factors over $\varphi$. Since $\pi_2$ is split epi, $\text{id}_U$ factors over $\pi_2$ and hence over $\varphi$, i.e. $\varphi$ is split epi. $\square$

We can now extend the notions of shard and shard-freedom to multipliers that are not $\top$-slice objectwise pointable without changing their meaning for those that are:

**Definition 3.4.9.** We say that a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice **shard-free** if $\nexists_U$ is essentially surjective on $\mathcal{V} // U$, the full subcategory of $\mathcal{V} / U$ of dimensionally split slice objects. A dimensionally split slice object $(V, \psi)$ that is not in the image of $\nexists_U$ even up to isomorphism, will be called a **shard** of the multiplier.

Note that a multiplier is $\top$-slice shard-free if every dimensionally split slice object has an *invertible* dimensional section.

17

**Theorem 3.4.10** ($\top$-slice quotient theorem$^{\S A}$). If a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice fully faithful and shard-free, then $\exists_U : \mathcal{W} \simeq \mathcal{V} // U$ is an equivalence of categories. $\square$

**Example 3.4.11** (Identity). In the category $\mathcal{W}$ with the identity multiplier $W \ltimes \top = W$, every morphism $W \to \top$ is dimensionally split with $\mathrm{id}_W$ as an invertible dimensional section. The multiplier is $\top$-slice fully faithful and shard-free, so the quotient theorem applies.

**Example 3.4.12** (Nullary cubes). In the categories of $k$-affine cubes $\square^k$ (example 3.3.3) and $k$-ary cartesian cubes $\square^k$ (example 3.3.4) ($k \geq 0$), a morphism $\varphi : \mathbb{I}^n \to \mathbb{I}$ is dimensionally split if $i_1 \langle \varphi \rangle$ is a variable. The multipliers $\sqcup * \mathbb{I} : \square^k \to \square^k$ and $\sqcup \times \mathbb{I} : \square^k \to \square^k$ are $\top$-slice shard-free. The multiplier for affine cubes is also $\top$-slice fully faithful so the quotient theorem applies.

**Example 3.4.13** (Clocks). In the category of clocks $\odot$ (example 3.3.6), a morphism $\varphi : V \to (i : \odot_k)$ is dimensionally split if $i \langle \varphi \rangle$ has clock type $\odot_k$. The multiplier $\sqcup \times (i : \odot_k)$ is $\top$-slice fully faithful and shard-free, so the quotient theorem applies.

**Example 3.4.14** (Embargoes). For the embargo multiplier $\sqcup \ltimes \mathbf{!} := (\mathrm{Id}, \top) : \mathcal{W} \to \mathcal{W} \times \uparrow$ (example 3.3.9) for $\mathbf{!} := (\top, \top)$, a morphism $((), ()) : (W, o) \to \mathbf{!}$ is dimensionally split if $o = \top$, with the identity as an invertible dimensional section. The multiplier $\sqcup \ltimes \mathbf{!}$ is $\top$-slice shard-free.

For $\sqcup \ltimes (\mathbf{!} \ltimes U) : (W, o) \mapsto (W \ltimes U, o)$, a morphism $(\varphi, ()) : (W, o) \to (U, \top) = (\mathbf{!} \ltimes U)$ is dimensionally split if $\varphi : W \to U$ is dimensionally split for $\sqcup \ltimes U$. If $\chi : W' \ltimes U \to W$ is a dimensional section for $\varphi$, then $(\chi, \mathrm{id}_o) : (W' \ltimes U, o) \to (W, o)$ is a dimensional section for $(\varphi, ())$. $\top$-slice shard-freedom is then inherited from $\sqcup \ltimes U$.

**Example 3.4.15** (Enhanced embargoes). For the enhanced embargo multiplier $\sqcup \ltimes \mathbf{!} : \mathcal{W} \to \mathcal{W}_\mathbf{I} = \mathcal{W}_\perp / \mathcal{W} : W \mapsto (W \xrightarrow{\mathrm{id}} W)$ (example 3.3.10), a morphism $(V \xrightarrow{\varphi} W) \to (\top \to \top) = \mathbf{!}$ is dimensionally split if $V \neq \perp$, with dimensional section $(\mathrm{id}_V, \varphi) : (V \to V) \to (V \xrightarrow{\varphi} W)$. This multiplier is generally not $\top$-slice shard-free: since it only produces identity arrows, any dimensionally split non-identity arrow is a shard.

For $\sqcup \ltimes (U \ltimes \mathbf{!}) : (V \to W) \mapsto (V \ltimes U \to W \ltimes U)$, a morphism $(V \to W) \to (U \to U) = (U \ltimes \mathbf{!})$ is dimensionally split (with section $([], \chi) : (\perp \to W' \ltimes U) \to (V \to W)$) if the morphism $W \to U$ is dimensionally split for $\sqcup \ltimes U$ with section $\chi : W' \ltimes U \to W$. The multiplier $\sqcup \ltimes (U \ltimes \mathbf{!})$ is generally not $\top$-slice shard-free, as the domain part of a dimensionally split morphism could be anything.

For $\sqcup \ltimes (\mathbf{!} \ltimes U) : (V \to W) \mapsto (V \ltimes U \to W)$, any morphism $(V \to W) \to (U \to \top) = (\mathbf{!} \ltimes U)$ is dimensionally split by

$$([], \mathrm{id}) : (\perp \to W) \ltimes (\mathbf{!} \ltimes U) = (\perp \to W) \to (V \to W). \quad (21)$$

This multiplier is therefore generally not $\top$-slice shard-free.

To conclude, we have made the base category more complicated in order to be able to define the latter multiplier, but as a trade-off we now have shards to deal with.

**Example 3.4.16** (Erasure). In the category $\mathrm{Erase}_d$ (example 3.3.12) with multiplier $\sqcup \times i$, all morphisms to $i$ are dimensionally split with the identity as an invertible dimensional section. The multiplier is shard-free.

### 3.4.4 Boundaries

**Definition 3.4.17.** The boundary $\partial U$ of a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is a presheaf over $\mathcal{V}$ such that the cells $V \Rightarrow \partial U$ are precisely the morphisms $V \to U$ that are *not* dimensionally split.

This is a valid presheaf by proposition 3.4.8.

**Proposition 3.4.18.** If $\sqcup \ltimes U$ is $\top$-slice objectwise pointable, then $\partial U$ is the largest strict subobject of $\mathbf{y}U$.

18

Proof. Recall that if the multiplier is $\top$-slice objectwise pointable, then dimensionally split and split epi are synonymous.

Clearly, $\partial U \subseteq \mathbf{y}U$. Since $\text{id} : U \to U$ is split epi, we have $\partial U \subsetneq \mathbf{y}U$. Now take another strict subobject $\Upsilon \subsetneq \mathbf{y}U$. We show that $\Upsilon \subseteq \partial U$.

We start by showing that $\text{id} \notin U \Rightarrow \Upsilon$. Otherwise, every $\varphi \in V \Rightarrow \mathbf{y}U$ would have to be a cell of $\Upsilon$ as it is a restriction of id, which would imply $\Upsilon = \mathbf{y}U$.

Now id is a restriction of any split epimorphism, so $\Upsilon$ contains no split epimorphisms, i.e. $\Upsilon \subseteq \partial U$.

Remark 3.4.19. $\top$-slice shard-freedom can also be formulated using (co)sieves [nLa23b]. A sieve in $\mathcal{W}$ is a full subcategory $\mathcal{S}$ such that if $W \in \mathcal{S}$ and $\varphi : V \to W$, then $V \in \mathcal{S}$. The dual (where $\varphi$ points the other way) is called a cosieve in $\mathcal{W}$. Being full subcategories, (co)sieves can be regarded as subsets of Obj$\mathcal{W}$. A sieve on $U \in \mathcal{W}$ is a sieve in $\mathcal{W}/U$ or, equivalently, a subpresheaf of $\mathbf{y}U$.

A multiplier is $\top$-slice shard-free if either of the following equivalent criteria is satisfied:

- The objects in the essential image of $\perp_U$ constitute a cosieve in $\mathcal{W}/U$ [Nuy23].
- The objects outside the essential image of $\perp_U$ constitute a sieve in $\mathcal{W}/U$, i.e. a sieve on $U$.

The slice objects of the cosieve generated by objects of the essential image of $\perp_U$, are called dimensionally split. The boundary $\partial U$ is the largest sieve on $U$ that is disjoint with the objects of the essential image of $\perp_U$.

If $\sqcup \ltimes U$ is $\top$-slice fully faithful, then the above conditions are furthermore equivalent to $\perp_U$ being a Street opfibration.

Example 3.4.20. In all the binary cube categories mentioned in section 3.3, $\partial \mathbb{I}$ is isomorphic to the constant presheaf of booleans.

For affine cubes, if we define a multiplier $\sqcup * \mathbb{I}^2$ in the obvious way, then $\partial \mathbb{I}^2$ is isomorphic to a colimit of four times $\mathbf{y}\mathbb{I}$ and four times $\mathbf{y}\top$, i.e. a square without filler. For cartesian asymmetric cubes, the square also gains a diagonal. For symmetric cubes (with an involution $\neg : \mathbb{I} \to \mathbb{I}$), the other diagonal also appears.

### 3.5 Acting on slice objects

Definition 3.5.1. Given a multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$, we define

$$\perp_U^{/W_0} : \mathcal{W}/W_0 \to \mathcal{V}/(W_0 \ltimes U) : (W, \psi) \mapsto (W \ltimes U, \psi \ltimes U), \tag{22}$$

which is an instance of definition 2.1.6. We say that $\sqcup \ltimes U$ is:

- Slicewise faithful$^{\S A}$ if for all $W_0$, the functor $\perp_U^{/W_0}$ is faithful,
- Slicewise full$^{\S A}$ if for all $W_0$, the functor $\perp_U^{/W_0}$ is full,
- Indirectly slicewise shard-free$^{\S A}$ (obsolete$^{12}$) if for all $W_0$, the functor $\perp_U^{/W_0}$ is essentially surjective on slice objects $(V, \varphi) \in \mathcal{V}/(W_0 \ltimes U)$ such that $\varphi$ is indirectly dimensionally split,

- We say that $\varphi : V \to W_0 \ltimes U$ is indirectly dimensionally split if $\pi_2 \circ \varphi : V \to U$ is dimensionally split.

- We point out that the full subcategory of such slice objects is isomorphic to $(\mathcal{V}//U)/(W_0 \ltimes U, \pi_2)$.

$^{12}$This was the original notion of shard-freedom$^{\S A}$, as referred to in [Nuy20], but it leads to a boundary predicate (definition 4.4.3) that is respected by the substitution functor $\Omega_{\mathbf{y}U}^{\Psi}$. This is in contrast to the transpension type, which in general is not respected by the substitution functor (it is if the multiplier is $\top$-slice fully faithful, see theorem 6.3.1). As a result, with this notion of indirect slicewise shard-freedom, the boundary theorem 4.4.5 can only be stated over $\top \ltimes \mathbf{y}U$ as opposed to general $\Psi \ltimes \mathbf{y}U$. For this reason, we prefer the notion of direct slicewise shard-freedom below.

19

- An indirectly dimensionally split slice object \((V, \psi) \in \mathcal{V} / W_0 \ltimes U\) that is not in the image of \(\exists_U^{W_0}\) even up to isomorphism, will be called an indirect shard\(^{\S A}\) of the multiplier.

- Directly slicewise shard-free\(^{\S A}\) if for all \(W_0\), the functor \(\exists_U^{W_0}\) is essentially surjective on slice objects \((V, \varphi) \in \mathcal{V}/(W_0 \ltimes U)\) such that \(\varphi: V \to W_0 \ltimes U\) is directly dimensionally split:

- We say that \(\varphi : V \to W_0 \ltimes U\) is directly dimensionally split with direct dimensional section \(\chi : W \ltimes U \to V\) if \(\varphi \circ \chi\) is of the form \(\psi \ltimes U\). The section can alternatively be presented as a morphism of slice objects \(\chi : \exists_U^{W_0}(W, \psi) \to (V, \varphi)\).
- We denote the full subcategory of directly dimensionally split slice objects as \(\mathcal{V} // (W_0 \ltimes U)\).
- A directly dimensionally split slice object \((V, \psi) \in \mathcal{V} / W_0 \ltimes U\) that is not in the image of \(\exists_U^{W_0}\) even up to isomorphism, will be called a direct shard\(^{\S A}\) of the multiplier.

- Slicewise right adjoint\(^{\S A}\) if for all \(W_0\), the functor \(\exists_U^{W_0}\) has a left adjoint \(\exists_U^{W_0}: \mathcal{V}/(W_0 \ltimes U) \to \mathcal{W}/W_0\). We denote the unit as \(\text{copy}_U^{W_0}: \text{Id} \to \exists_U^{W_0} \exists_U^{W_0}\) and the co-unit as \(\text{drop}_U^{W_0}: \exists_U^{W_0} \exists_U^{W_0} \to \text{Id}\).

The above definition generalizes the functor \(\exists_U\) that we already had:

Proposition 3.5.2. The functor \(\exists_U^{\top}:\mathcal{W} / \top \to \mathcal{V} / (\top \ltimes U)\) is equal to \(\exists_U:\mathcal{W}\to \mathcal{V} / U\) over the obvious isomorphisms between their domains and codomains. Hence, each of the slicewise properties implies the \(\top\)-slice property. (Both notions of slicewise shard-freedom imply basic shard-freedom.)

Note that both notions of slicewise shard-freedom are well-defined:

Proposition 3.5.3. 1. (Obsolete.) The functor \(\exists_U^{W_0}\) factors over \((\mathcal{V} // U) / (W_0 \ltimes U, \pi_2)\).

2. The functor \(\exists_U^{W_0}\) factors over \(\mathcal{V} // (W_0 \ltimes U)\).
3. Directly dimensionally split morphisms are indirectly dimensionally split with the same section. As such, there is a functor \(\mathcal{V} // (W_0 \ltimes U) \to (\mathcal{V} // U) / (W_0 \ltimes U, \pi_2)\). Hence, direct shards are indirect shards and indirect slicewise shard-freedom implies direct slicewise shard-freedom.

Proof. 1. The functor \(\exists_U^{W_0}\) sends \((W,\psi)\) to \((W\times U,\psi\times U)\). Since \(\pi_2\circ (\psi \ltimes U) = \pi_2\), it is dimensionally split with the identity as a section.

2. The identity is a direct dimensional section.
3. Let \(\varphi : V \to W_0 \ltimes U\) be directly dimensionally split with section \(\chi\), i.e. \(\varphi \circ \chi = \psi \ltimes U\). Then \(\pi_2 \circ \varphi \circ \chi = \pi_2 \circ (\psi \ltimes U) = \pi_2\), so \(\pi_2 \circ \varphi\) is dimensionally split with section \(\chi\).

Proposition 3.5.4. If \(\sqcup \ltimes U:\mathcal{W}\to \mathcal{V}\) is \(\top\) -slice faithful, then it is slicewise faithful.

Proof. Pick morphisms \(\varphi, \chi : (W, \psi) \to (W', \psi')\) in \(\mathcal{W}/W_0\) such that \(\exists_U^{W_0} \varphi = \exists_U^{V} \chi\). Expanding the definition of \(\exists_U^{W_0}\), we see that this means that \(\varphi \ltimes U = \chi \ltimes U\), and hence \(\varphi = \chi\) by faithfulness of \(\sqcup \ltimes U\) (lemma 3.2.2).

Proposition 3.5.5. If \(\sqcup \ltimes U:\mathcal{W}\to \mathcal{V}\) is \(\top\) -slice fully faithful, then it is slicewise full.

Proof. Pick \((W, \psi)\) and \((W', \psi')\) in \(\mathcal{W}/W_0\), and a morphism \(\chi: \exists_U^{W_0}(W, \psi) \to \exists_U^{W_0}(W', \psi')\). This amounts to a diagram:

![img-6.jpeg](img-6.jpeg)

20

i.e. a triangle in $\mathcal{W}/U$, the objects of which are in the image of $\mathbb{J}_U : \mathcal{W} \to \mathcal{W}/U$. Then, by fullness of $\mathbb{J}_U$ we get $\chi_0 : W \to W'$ such that $\mathbb{J}_U \chi_0 = \chi$, which by faithfulness of $\mathbb{J}_U$ makes the following diagram commute:

$$\begin{array}{c} W \xrightarrow{\chi_0} W' \\ \psi \searrow \searrow \searrow \psi' \\ W_0 \end{array} \tag{24}$$

Then $\chi_0$ is a morphism $\chi_0 : (W, \psi) \to (W', \psi')$ in $\mathcal{W}/W_0$ and $\mathbb{J}_U^{W_0} \chi_0 = \chi$.

**Proposition 3.5.6.** 1. If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice full, then direct and indirect dimensional splitness are equivalent, with the same dimensional sections.

2. (Obsolete.) If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice full and shard-free, then it is indirectly slicewise shard-free.
3. If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice full and shard-free, then it is directly slicewise shard-free.

*Proof.* 1. We already know that direct dimensional splitness implies indirect dimensional splitness with the same section (proposition 3.5.3). We prove the other implication.

Pick some $(V, \varphi) \in \mathcal{V}/(W_0 \ltimes U)$ such that $\pi_2 \circ \varphi : V \to U$ is dimensionally split with section $\chi : W \ltimes U \to V$. Because $\mathbb{J}_U$ is full, there is a morphism $\psi : W \to W_0$ such that $\psi \ltimes U = \varphi \circ \chi : W \ltimes U \to W_0 \ltimes U$. Thus, $\varphi$ is directly dimensionally split.

$$\begin{array}{c} V \xleftarrow{\chi} W \ltimes U \\ \varphi \searrow \searrow \searrow \psi \ltimes U \\ W_0 \ltimes U \\ \downarrow \pi_2 \\ U \end{array} \tag{25}$$

2. Pick some $(V, \varphi) \in \mathcal{V}/(W_0 \ltimes U)$ such that $\pi_2 \circ \varphi : V \to U$ is dimensionally split. Because $\mathbb{J}_U$ is essentially surjective on $\mathcal{V}//U$, there must be some $W \in \mathcal{W}$ such that $\iota : \mathbb{J}_U W = (W \ltimes U, \pi_2) \cong (V, \pi_2 \circ \varphi)$ as slice objects over $U$. Because $\mathbb{J}_U$ is full, there is a morphism $\psi : W \to W_0$ such that $\psi \ltimes U = \varphi \circ \iota : W \ltimes U \to W_0 \ltimes U$. Thus, $\iota^{-1} : (V, \varphi) \cong (W \ltimes U, \psi \ltimes U) = \mathbb{J}_U^{W_0}(W, \psi)$ as slice objects over $W_0 \ltimes U$.

$$\begin{array}{c} V \xleftarrow{\iota} W \ltimes U \\ \varphi \searrow \searrow \searrow \psi \ltimes U \\ W_0 \ltimes U \\ \downarrow \pi_2 \\ U \end{array} \tag{26}$$

3. Since indirect slicewise shard-freedom implies direct slicewise shard-freedom (proposition 3.5.3).

**Example 3.5.7** (Obsolete). In the category $\square^k$ of $k$-ary cartesian cubes (example 3.3.4), the diagonal $\delta : \mathbb{I} \to \mathbb{I} \times \mathbb{I}$ has the property that $\pi_2 \circ \delta$ is split epi, but $(\mathbb{I}, \delta)$ is not in the image of $\mathbb{J}_\mathbb{I}^1$. Thus, $\sqcup \ltimes \mathbb{I}$ is not *indirectly* slicewise shard-free, despite being $\top$-slice shard-free.

**Proposition 3.5.8.** If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice right adjoint, then it is slicewise right adjoint, with

$$\exists_U^{W_0}(V, \varphi) = (\exists_U(V, \pi_2 \circ \varphi), \mathsf{drop}_U \circ \exists_U \varphi),$$

21

$$\begin{aligned} \text{drop}_U^{W_0}(W, \psi) &= \text{drop}_U W : \exists_U^{W_0} \neg_U^{W_0}(W, \psi) \to (W, \psi), \\ \text{copy}_U^{W_0}(V, \varphi) &= \text{copy}_U(V, \pi_2 \circ \varphi) : (V, \varphi) \to \neg_U^{W_0} \exists_U^{W_0}(V, \varphi). \end{aligned}$$

*Proof.* Note that a slice category over a slice category is just a slice category, i.e. $(\mathcal{C}/y)/(x, \varphi) \cong \mathcal{C}/x$. In this light, the functor $\neg_U^{W_0}$ is not just the action of $\sqcup \ltimes U$ on slice objects over $W_0$, but also the action of $\neg_U$ on slice objects over $W_0$. Now since $\neg_U$ has left adjoint $\exists_U$, we get a left adjoint to $\neg_U^{W_0}$ by proposition 2.1.7. $\square$

**Proposition 3.5.9** (Functoriality of the slice category). A morphism of multipliers $\sqcup \ltimes v : \sqcup \ltimes U \to \sqcup \ltimes U'$ gives rise to a natural transformation $\Sigma^{W_0 \ltimes v} \circ \neg_U^{W_0} \to \neg_U^{W_0}$. Hence, if both multipliers are $\top$-slice (or equivalently slicewise) right adjoint, we also get $\exists_U^{W_0} \circ \Sigma^{W_0 \ltimes v} \to \exists_U^{W_0}$.

*Proof.* For any $(W, \psi) \in \mathcal{W}/W_0$, we have to prove $(W \ltimes U, (W_0 \ltimes v) \circ (\psi \ltimes U)) \to (W \ltimes U', \psi \ltimes U')$. The morphism $W \ltimes v : W \ltimes U \to W \ltimes U'$ does the job. The second statement follows from lemma 2.1.1. $\square$

**Theorem 3.5.10** (Slicewise quantification theorem). If $\sqcup \ltimes U$ is

1. $\top$-slice (or equivalently slicewise) fully faithful and right adjoint, then we have a natural isomorphism $\text{drop}_U^{W_0} : \exists_U^{W_0} \neg_U^{W_0} \cong \text{Id}$.
2. copointed, then we have

- (a) $\text{hide}_U^{W_0} : \Sigma_U^{W_0} \to \exists_U^{W_0}$ (if $\top$-slice, or equivalently presheafwise, right adjoint),
- (b) $\text{spoil}_U^{W_0} : \neg_U^{W_0} \to \Omega_U^{W_0}$ (if $\Omega_U^{W_0}$ exists),
- (c) in any case $\Sigma_U^{W_0} \neg_U^{W_0} \to \text{Id}$.

3. a comonad, then there is a natural transformation $\Sigma^{W_0 \ltimes \delta} \circ \neg_U^{W_0} \to \neg_{U \ltimes U}^{W_0}$, where we compose multipliers as in theorem 3.6.1.
4. cartesian, then we have natural isomorphisms:

- (a) $\exists_U^{W_0}(V, \varphi) \cong \Sigma_U^{W_0}(V, \varphi) = (V, \pi_1 \circ \varphi)$,
- (b) $\neg_U^{W_0}(W, \psi) \cong \Omega_U^{W_0}(W, \psi)$,
- (c) $\exists_U^{W_0} \neg_U^{W_0}(W, \psi) \cong \Sigma_U^{W_0} \Omega_U^{W_0}(W, \psi) \cong (W \ltimes U, \psi \circ \pi_1)$.

Moreover, these isomorphisms become equality if $\exists_U^{W_0}$ is constructed from $\exists_U = \Sigma_U$ as in the proof of proposition 3.5.8, and $\Omega_U^{W_0}(W, \psi)$ is chosen wisely. (Both functors are defined only up to isomorphism.)

*Proof.* 1. This is a standard fact about fully faithful right adjoints such as $\neg_U^{W_0}$.

2. By lemma 2.1.1, it is sufficient to prove $\Sigma_U^{W_0} \neg_U^{W_0} \to \text{Id}$, and indeed we have

$$\pi_1 : \Sigma_U^{W_0} \neg_U^{W_0}(W, \psi) = (W \ltimes U, \pi_1 \circ (\psi \ltimes U)) = (W \ltimes U, \psi \circ \pi_1) \to (W, \psi).$$

3. This is a special case of proposition 3.5.9.
4. (a) The isomorphism is obtained from the next point by uniqueness of adjoints. We prove the equality if $\exists_U = \Sigma_U$. The co-unit is then given by $\text{drop}_U = \pi_1 : W \ltimes U \to W$. The construction of $\exists_U^{W_0}$ then reveals that $\exists_U^{W_0}(V, \varphi) = (V, \pi_1 \circ \varphi)$, which is the definition of $\Sigma_U^{W_0}(V, \varphi)$.
5. (b) This follows from the definitions.

22

(c) We have

$$\exists_{U}^{W_0} \exists_{U}^{W_0}(W, \psi) = \exists_{U}^{W_0}(W \times U, \psi \times U) \cong (W \times U, \pi_1 \circ (\psi \times U)) = (W \times U, \psi \circ \pi_1). \ \square$$

**Theorem 3.5.11** (Slicewise quotient theorem$^{8/9}$). If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice (or equivalently slicewise, for either notion of shard-freedom) fully faithful and shard-free, then

1. (Obsolete.) $\exists_{U}^{W_0} : \mathcal{W}/W_0 \simeq (\mathcal{V}//U)/(W_0 \ltimes U, \pi_2)$ is an equivalence of categories,$^{13}$

2. $\exists_{U}^{W_0} : \mathcal{W}/W_0 \simeq \mathcal{V}//(W_0 \ltimes U)$ is an equivalence of categories.

### 3.6 Composing multipliers

**Theorem 3.6.1.** If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is a multiplier for $U$ and $\sqcup \ltimes U' : \mathcal{V} \to \mathcal{V}'$ is a multiplier for $U'$, then their composite $\sqcup \ltimes (U \ltimes U') := (\sqcup \ltimes U) \ltimes U'$ is a multiplier for $U \ltimes U'$.

1. The functor $\exists_{U \ltimes U'} : \mathcal{W} \to \mathcal{V}'/(U \ltimes U')$ equals $\exists_{U'}^{U'} \circ \exists_{U}$.

2. The functor $\exists_{U \ltimes U'}^{W_0} : \mathcal{W} \to \mathcal{V}'/(U \ltimes U')$ equals $\exists_{U'}^{W_0 \ltimes U} \circ \exists_{U}^{W_0}$.

3. Assume both multipliers are endo. Then:

(a) The composite $\sqcup \ltimes (U \ltimes U')$ is copointed if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are copointed,

(b) The composite $\sqcup \ltimes (U \ltimes U')$ is a comonad if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are comonads,

(c) The composite $\sqcup \ltimes (U \ltimes U')$ is cartesian if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are cartesian.

4. The composite $\sqcup \ltimes (U \ltimes U')$ is $\top$-slice faithful if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are $\top$-slice faithful.

5. The composite $\sqcup \ltimes (U \ltimes U')$ is $\top$-slice full if $\sqcup \ltimes U$ is $\top$-slice full and $\sqcup \ltimes U'$ is slicewise full.

6. The composite $\sqcup \ltimes (U \ltimes U')$ is slicewise full if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are slicewise full.

7. The composite $\sqcup \ltimes (U \ltimes U')$ is $\top$-slice shard-free if $\sqcup \ltimes U$ is $\top$-slice shard-free and $\sqcup \ltimes U'$ is slicewise full and shard-free.

8. (a) (Obsolete). The composite $\sqcup \ltimes (U \ltimes U')$ is indirectly slicewise shard-free if $\sqcup \ltimes U$ is indirectly slicewise shard-free and $\sqcup \ltimes U'$ is slicewise full and indirectly slicewise shard-free.

(b) The composite $\sqcup \ltimes (U \ltimes U')$ is directly slicewise shard-free if $\sqcup \ltimes U$ is directly slicewise shard-free and $\sqcup \ltimes U'$ is slicewise full and directly slicewise shard-free.

9. The composite $\sqcup \ltimes (U \ltimes U')$ is $\top$-slice right adjoint if $\sqcup \ltimes U$ and $\sqcup \ltimes U'$ are $\top$-slice right adjoint, and in that case we have:

(a) $\exists_{U \ltimes U'} = \exists_{U} \circ \exists_{U'}^{U}$,

(b) $\exists_{U \ltimes U'}^{W_0} = \exists_{U}^{W_0} \circ \exists_{U'}^{W_0 \ltimes U}$.

*Proof.* Since $\top \ltimes U \cong U$, we see that $(\top \ltimes U) \ltimes U' \cong U \ltimes U'$, so the composite is indeed a multiplier for $U \ltimes U'$.

1-2. Follows from expanding the definitions.

3. (a) Copointed endofunctors compose.

(b) Comonads compose. They most certainly do not!

(c) By associativity of the cartesian product.

$^{13}$We use a slight abuse of notation by using $(\mathcal{V}//U)/(W_0 \ltimes U, \pi_2)$ as a subcategory of $\mathcal{V}/(W_0 \ltimes U)$.

23

4. $\top$-slice faithful multipliers are slicewise faithful (proposition 3.5.4), and the composite $\exists_{U \ltimes U'} = \exists_{U'}^{U} \exists_U$ of faithful functors is faithful.

5-6. Follows from the first two properties, since the composite of full functors is full.

7. Analogous to the next point, with $W_0 = \top$.

8. Recall that the assumptions imply that $\sqcup \ltimes U'$ is slicewise fully faithful and slicewise indirectly and directly shard-free.

(a) Pick a slice object $(V', \varphi') \in \mathcal{V}'/(W_0 \ltimes U \ltimes U')$ such that $\pi_2^{U \ltimes U'} \circ \varphi' : V' \to U \ltimes U'$ is dimensionally split with section $\chi' : W_1 \ltimes U \ltimes U' \to V'$. Then $\pi_2^{U'} \circ \pi_2^{U \ltimes U'} \circ \varphi' = \pi_2^{U'} \circ \varphi' : V' \to U'$ is also dimensionally split with the same section.

Because $\sqcup \ltimes U'$ is indirectly slicewise shard-free, we find some $(V, \varphi) \in \mathcal{V}/(W_0 \ltimes U)$ such that $\iota' : (V', \varphi') \cong \exists_{U'}^{W_0 \ltimes U} (V, \varphi) \in \mathcal{V}'/(W_0 \ltimes U \ltimes U')$.

![img-7.jpeg](img-7.jpeg)

![img-8.jpeg](img-8.jpeg)

Note that $\pi_2^{U \ltimes U'} = \pi_2^U \ltimes U'$. Because $\exists_{U'}^{U}$ is full, the morphism $\iota' \circ \chi' : \exists_{U'}^{U} (W_1 \ltimes U, \pi_2^U) \to \exists_{U'}^{U} (V, \pi_2^U \circ \varphi)$ has a preimage $\chi : (W_1 \ltimes U, \pi_2^U) \to (V, \pi_2^U \circ \varphi)$ under $\exists_{U'}^{U}$. Thus, we see that $\pi_2 \circ \varphi : V \to U$ is dimensionally split. Because $\sqcup \ltimes U$ is indirectly slicewise shard-free, we find some slice object $(W, \psi) \in \mathcal{W}/W_0$ so that $\iota : (V, \varphi) \cong \exists_{U'}^{W_0} (W, \psi) \in \mathcal{V}/(W_0 \ltimes U)$. We conclude that

$$(V', \varphi') \cong \exists_{U'}^{W_0 \ltimes U} (V, \varphi) \cong \exists_{U'}^{W_0 \ltimes U} \exists_{U'}^{W_0} (W, \psi) = \exists_{U \ltimes U'}^{W_0} (W, \psi). \tag{27}$$

(b) Pick a slice object $(V', \varphi') \in \mathcal{V}'/(W_0 \ltimes U \ltimes U')$ that is directly dimensionally split for the composite multiplier with section $\chi' : W_1 \ltimes U \ltimes U' \to V'$, composing to $\varphi' \circ \chi' = \psi_1 \ltimes U \ltimes U'$. Then $\varphi'$ is also directly dimensionally split for $\sqcup \ltimes U'$.

Because $\sqcup \ltimes U'$ is directly slicewise shard-free, we find some $(V, \varphi) \in \mathcal{V}/(W_0 \ltimes U)$ such that $\iota' : (V', \varphi') \cong \exists_{U'}^{W_0 \ltimes U} (V, \varphi) \in \mathcal{V}'/(W_0 \ltimes U \ltimes U')$.

![img-9.jpeg](img-9.jpeg)

![img-10.jpeg](img-10.jpeg)

24

Because $\exists_{U'}^{W_0 \ltimes U}$ is full, the morphism $\iota' \circ \chi' : \exists_{U'}^{W_0 \ltimes U}(W_1 \ltimes U, \psi_1 \ltimes U) \to \exists_{U'}^{W_0 \ltimes U}(V, \varphi)$ has a preimage $\chi : (W_1 \ltimes U, \psi_1 \ltimes U) \to (V, \varphi)$ under $\exists_{U'}^{W_0 \ltimes U}$. Thus, we see that $\varphi : V \to U$ is directly dimensionally split with section $\chi$. Because $\sqcup \ltimes U$ is directly slicewise shard-free, we find some slice object $(W, \psi) \in \mathcal{W}/W_0$ so that $\iota : (V, \varphi) \cong \exists_{U'}^{W_0}(W, \psi) \in \mathcal{V}/(W_0 \ltimes U)$. We conclude that

$$(V', \varphi') \cong \exists_{U'}^{W_0 \ltimes U}(V, \varphi) \cong \exists_{U'}^{W_0 \ltimes U} \exists_{U'}^{W_0}(W, \psi) = \exists_{U \ltimes U'}^{W_0}(W, \psi). \quad (28)$$

9. $\top$-slice right adjoint multipliers are slicewise right adjoint (proposition 3.5.8), and the composite of the left adjoints is a left adjoint to the composite. $\square$

## 4 Multipliers and presheaves

**Definition 4.0.1.** Every multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ gives rise to three adjoint endofunctors between $\widehat{\mathcal{W}}$ and $\widehat{\mathcal{V}}$ via theorem 2.3.2, which we will denote

$$(\sqcup \ltimes \mathbf{y}U) \dashv (\mathbf{y}U \multimap \sqcup) \dashv (\mathbf{y}U \swarrow \sqcup). \quad (29)$$

Correspondingly, a morphism of multipliers $\sqcup \ltimes v$ gives rise to natural transformations $\sqcup \ltimes \mathbf{y}v, \mathbf{y}v \multimap \sqcup$ and $\mathbf{y}v \swarrow \sqcup$.

We will not actually be using the latter two of these functors, although they can be retrieved at least up to isomorphism from the functors in definitions 2.3.17 and 4.3.1 via the equation $\sqcup \ltimes U = \Sigma_U \exists_U$.

Note that the functor $\sqcup \ltimes \mathbf{y}U : \widehat{\mathcal{W}} \to \widehat{\mathcal{V}}$ is quite reminiscent of the Day-convolution with $\mathbf{y}U$, which is the reason for our choice of notation. However, each of the notations is to be regarded as a single symbol, i.e. $\ltimes$, $\multimap$ and $\swarrow$ by themselves have no meaning.

### 4.1 Acting on elements

In section 3.5, we generalized $\exists_U : \mathcal{W} \to \mathcal{V}/U$ to act on slice objects as $\exists_{U'}^{W_0} : \mathcal{W}/W_0 \to \mathcal{V}/(W_0 \ltimes U)$. Here, we further generalize to a functor whose domain is the category of elements:

**Definition 4.1.1.** We define (using notation 2.3.3):

- $\exists_{U'}^{\Psi} : \mathcal{W}/\Psi \to \mathcal{V}/(\Psi \ltimes \mathbf{y}U) : (W, \psi) \mapsto (W \ltimes U, \psi \ltimes \mathbf{y}U)$,
- $\exists_{U}^{\in \Psi} : (W \Rightarrow \Psi) \to \{\varphi : W \ltimes U \Rightarrow \Psi \ltimes \mathbf{y}U \mid \pi_2 \circ \varphi = \pi_2 : W \ltimes U \to U\} : \psi \mapsto \psi \ltimes \mathbf{y}U$.

We say that $\sqcup \ltimes U$ is:

- **Presheafwise faithful**$^{\S A}$ if for all $\Psi$, the functor $\exists_{U'}^{\Psi}$ is faithful,
- $\top$-slice elementally faithful$^{\S A}$ if for all $\Psi$, the natural transformation $\exists_{U}^{\in \Psi}$ is componentwise injective,
- **Presheafwise full**$^{\S A}$ if for all $\Psi$, the functor $\exists_{U'}^{\Psi}$ is full,
- $\top$-slice elementally full$^{\S A}$ if for all $\Psi$, the natural transformation $\exists_{U}^{\in \Psi}$ is componentwise surjective,
- **Indirectly presheafwise shard-free**$^{\S A}$ (obsolete$^{14}$) if for all $\Psi$, the functor $\exists_{U'}^{\Psi}$ is essentially surjective on elements $(V, \varphi) \in \mathcal{V}/(\Psi \ltimes \mathbf{y}U)$ such that $\varphi$ is indirectly dimensionally split:

- We say that $\varphi : V \Rightarrow \Psi \ltimes \mathbf{y}U$ is **indirectly dimensionally split** if $\pi_2 \circ \varphi : V \to U$ is dimensionally split.

$^{14}$see definition 3.5.1

25

- An indirectly dimensionally split element \((V, \psi) \in \mathcal{V} / (\Psi \ltimes \mathbf{y}U)\) that is not in the image of \(\exists_{U}^{\prime \Psi}\) even up to isomorphism, will be called an indirect shard\(^{\S A}\) of the multiplier.

- Directly presheafwise shard-free\(^{\S A}\) if for all \(\Psi\), the functor \(\exists_{U}^{\prime \Psi}\) is essentially surjective on elements \((V, \varphi) \in \mathcal{V} / (\Psi \ltimes \mathbf{y}U)\) such that \(\varphi: V \to \Psi \ltimes \mathbf{y}U\) is directly dimensionally split:

- We say that \(\varphi : V \Rightarrow \Psi \ltimes \mathbf{y}U\) is directly dimensionally split with direct dimensional section \(\chi : W \ltimes U \to V\) if \(\varphi \circ \chi\) is of the form \(\psi \ltimes \mathbf{y}U\). The section can alternatively be presented as a morphism of elements \(\chi : \exists_{U}^{\prime \Psi}(W, \psi) \to (V, \varphi)\).

- We denote the full subcategory of directly dimensionally split elements as \(\mathcal{V} // (\Psi \ltimes \mathbf{y}U)\).

- A directly dimensionally split element \((V, \psi) \in \mathcal{V} / (\Psi \ltimes \mathbf{y}U)\) that is not in the image of \(\exists_{U}^{\prime \Psi}\) even up to isomorphism, will be called a direct shard\(^{\S A}\) of the multiplier.

- Presheafwise right adjoint\(^{\S A}\) if for all \(\Psi\), the functor \(\exists_{U}^{\prime \Psi}\) has a left adjoint \(\exists_{U}^{\prime \Psi}: \mathcal{V}/(\Psi \ltimes \mathbf{y}U) \to \mathcal{W}/\Psi\). We denote the unit as \(\text{copy}_{U}^{\prime \Psi}: \text{Id} \to \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi}\) and the co-unit as \(\text{drop}_{U}^{\prime \Psi}: \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi} \to \text{Id}\).

This is indeed a generalization:

Proposition 4.1.2. The functor \(\exists_{U}^{\prime \mathbf{y}W_0}: \mathcal{W} / \mathbf{y}W_0 \to \mathcal{V} / (\mathbf{y}W_0 \ltimes \mathbf{y}U)\) is equal to \(\exists_{U}^{\prime W_0}: \mathcal{W} / W_0 \to \mathcal{V} / (W_0 \ltimes U)\) over the obvious isomorphisms between their domains and codomains. Hence, each of the presheafwise notions implies the slicewise notion (definition 3.5.1). Moreover, each of the \(\top\)-slice elemental notions implies the basic \(\top\)-slice notion.

Proof. Most of this is straightforward after extracting the construction of the isomorphism \(\mathbf{y}W_0\times \mathbf{y}U\cong\) \(\mathbf{y}(W_0\times U)\) from the proof of theorem 2.3.2. To see the last claim, note that

\[
\{\varphi : W \ltimes U \Rightarrow \mathbf {y} W _ {0} \ltimes \mathbf {y} U | \pi_ {2} \circ \varphi = \pi_ {2} \} \cong ((W \ltimes U, \pi_ {2}) \rightarrow (W _ {0} \ltimes U, \pi_ {2})) = (\lrcorner_ {U} W \rightarrow \lrcorner_ {U} W _ {0}).
\]

So if injectivity/surjectivity holds for all W and  \( W_{0} \) , then we can conclude that  \( \perp_{U} \)  is faithful/full. ☐

Note that both notions of presheafwise shard-freedom are well-defined:

Proposition 4.1.3. 1. (Obsolete.) The functor \(\exists_{U}^{\prime \Psi}\) produces indirectly dimensionally split elements.

2. The functor \(\exists_{U}^{\prime \Psi}\) produces directly dimensionally split elements.

3. Directly dimensionally split elements are indirectly dimensionally split with the same section. Hence, direct shards are indirect shards and indirect presheafwise shard-freedom implies direct presheafwise shard-freedom.

Proof. See proposition 3.5.3.

Proposition 4.1.4. If \(\sqcup \ltimes U\) is \(\top\)-slice faithful, then it is presheafwise faithful.

Proof. Analogous to proposition 3.5.4.

Proposition 4.1.5. If \(\sqcup \ltimes U\) is \(\top\)-slice fully faithful, then it is \(\top\)-slice elementally faithful.

Proof. We have

\[
\begin{array}{l} \{\varphi : W \ltimes U \Rightarrow \Psi \ltimes \mathbf {y} U \mid \pi_ {2} \circ \varphi = \pi_ {2} \} \\ \cong \exists W _ {0}. (\varphi^ {\prime}: W \ltimes U \to W _ {0} \ltimes U) \times (\psi : W _ {0} \Rightarrow \Psi) \times (\pi_ {2} \circ (\psi \ltimes \mathbf {y} U) \circ \varphi^ {\prime} = \pi_ {2}) \\ \cong \exists W _ {0}. (\varphi^ {\prime}: W \ltimes U \to W _ {0} \ltimes U) \times (\psi : W _ {0} \Rightarrow \Psi) \times (\pi_ {2} \circ \varphi^ {\prime} = \pi_ {2}) \\ \cong \exists W _ {0}. (\varphi^ {\prime}: \mathbb {1} _ {U} W \rightarrow \mathbb {1} _ {U} W _ {0}) \times (\psi : W _ {0} \Rightarrow \Psi) \tag {30} \\ \end{array}
\]

and

\[
(W \Rightarrow \Psi) \cong \exists W _ {0}. (W \rightarrow W _ {0}) \times (W _ {0} \Rightarrow \Psi). \tag {31}
\]

26

Moreover, the action of $\mathbb{J}_U^{\in \Psi}$ sends $(W_0, \chi, \psi)$ in eq. (31) to $(W_0, \mathbb{J}_U\chi, \psi)$ in eq. (30). Naively, one would say that this proves injectivity, but some care is required with the equality relation for co-ends. It might be that $(W_0, \chi, \psi)$ and $(W_0, \chi', \psi)$ are sent to the same object. This would mean that there exists a zigzag $\zeta$ from $W_0$ to itself and jagwise morphisms $\mathbb{J}_UW \to \mathbb{J}_U\zeta$ (a priori not necessarily in the image of $\mathbb{J}_U$ which is why we need $\top$-slice fullness) and jagwise cells $\zeta \Rightarrow \Psi$ such that the following diagrams commute:

![img-11.jpeg](img-11.jpeg)

![img-12.jpeg](img-12.jpeg)

(32)

Then by full faithfulness of $\mathbb{J}_U$, we see that the unique preimage of the left triangle exists and also commutes and hence $\psi \circ \chi = \psi \circ \chi'$, so that $(W_0, \chi, \psi) = (W, \mathrm{id}, \psi \circ \chi) = (W, \mathrm{id}, \psi \circ \chi') = (W_0, \chi', \psi)$. $\square$

**Proposition 4.1.6.** If $\sqcup \ltimes U$ is $\top$-slice fully faithful, then it is presheafwise full.

*Proof.* Pick $(W, \psi)$ and $(W', \psi')$ in $\mathcal{W}/\Psi$ and a morphism $\chi : \mathbb{J}_U^{\upharpoonright\Psi}(W, \psi) \to \mathbb{J}_U^{\upharpoonright\Psi}(W', \psi')$. Then we also have $\chi : \mathbb{J}_UW \to \mathbb{J}_UW'$ and by fullness, we find a preimage $\chi_0 : W \to W'$ under $\mathbb{J}_U$. We have $(\psi' \ltimes \mathbf{y}U) \circ \chi = \psi \ltimes \mathbf{y}U$, so by $\top$-slice elemental faithfulness, we see that $\psi' \circ \chi_0 = \psi$, so that $\chi_0$ is a morphism of slice objects $\chi_0 : (W, \psi) \to (W', \psi') \in \mathcal{W}/\Psi$ and $\mathbb{J}_U^{\upharpoonright\Psi}\chi_0 = \chi$. $\square$

**Proposition 4.1.7.** If $\sqcup \ltimes U$ is $\top$-slice full, then it is $\top$-slice elementally full.

*Proof.* In the proof of proposition 4.1.5, we saw that $\mathbb{J}_U^{\in \Psi}$ essentially sends $(W_0, \chi, \psi_0)$ to $(W_0, \mathbb{J}_U\chi, \psi_0)$. Then if $\mathbb{J}_U\chi$ is full, it is immediate that this operation is surjective. $\square$

**Proposition 4.1.8.** 1. If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice full, then direct and indirect dimensional splitness are equivalent, with the same dimensional sections.

2. (Obsolete.) If $\sqcup \ltimes U$ is indirectly slicewise shard-free, then it is indirectly presheafwise shard-free.
3. If $\sqcup \ltimes U$ is $\top$-slice full and shard-free, then it is directly presheafwise shard-free.

*Proof.* 1. We already know that direct dimensional splitness implies indirect dimensional splitness with the same section (proposition 3.5.3). We prove the other implication.

Pick some $(V, \varphi) \in \mathcal{V}/(\Psi \ltimes \mathbf{y}U)$ that is indirectly dimensionally split with section $\chi$. By $\top$-slice elemental fullness, there is a cell $\psi : W \Rightarrow \Psi$ such that $\psi \ltimes \mathbf{y}U = \varphi \circ \chi : W \ltimes U \Rightarrow \Psi \ltimes \mathbf{y}U$. Then $\varphi$ is directly dimensionally split with section $\chi$.

![img-13.jpeg](img-13.jpeg)

2. Pick a slice object $(V, \varphi) \in \mathcal{V}/(\Psi \ltimes \mathbf{y}U)$ such that $\pi_2 \circ \varphi$ is dimensionally split. By definition of $\sqcup \ltimes \mathbf{y}U$, there is some $W_0$ such that $\varphi$ factors as $\varphi = (\psi^{W_0 \Rightarrow \Psi} \ltimes \mathbf{y}U) \circ \chi$. Clearly, $\pi_2 \circ \varphi = \pi_2 \circ \chi$ is dimensionally split. Hence, by indirect slicewise shard-freedom, $(V, \chi) \cong \mathbb{J}_U^{\upharpoonright W_0}(W, \chi') \in \mathcal{V}/(W_0 \ltimes U)$ for some $(W, \chi') \in \mathcal{W}/W_0$. Then we also have $(V, \varphi) = (V, (\psi \ltimes \mathbf{y}U) \circ \chi) \cong \mathbb{J}_U^{\upharpoonright \Psi}(W, \psi \circ \chi')$.

27

3. Pick some \((V, \varphi) \in \mathcal{V} / (\Psi \ltimes \mathbf{y}U)\) that is directly dimensionally split. Then \(\pi_2 \circ \varphi\) is dimensionally split. Because \(\exists_U\) is essentially surjective on \(\mathcal{V} // U\), there must be some \(W \in \mathcal{W}\) such that \(\iota : \exists_U W = (W \ltimes U, \pi_2) \cong (V, \pi_2 \circ \varphi)\) as slice objects over \(U\). By \(\top\)-slice elemental fullness, there is a cell \(\psi : W \Rightarrow \Psi\) such that \(\psi \ltimes \mathbf{y}U = \varphi \circ \iota : W \ltimes U \Rightarrow \Psi \ltimes \mathbf{y}U\). Thus, \(\iota^{-1} : (V, \varphi) \cong (W \ltimes U, \psi \ltimes \mathbf{y}U) = \exists_U^{/\Psi}(W, \psi)\) as slice objects over \(\Psi \ltimes \mathbf{y}U\).

![img-14.jpeg](img-14.jpeg)

Proposition 4.1.9. If \(\sqcup \ltimes U\) is \(\top\)-slice right adjoint, then it is presheafwise right adjoint, with

\[
\begin{array}{l} \exists_ {U} ^ {/ \Psi} (V, (\psi \ltimes \mathbf {y} U) \circ \varphi_ {0}) = \Sigma^ {/ \psi} \exists_ {U} ^ {/ W _ {0}} (V, \varphi_ {0}), \\ \operatorname{drop} _ {U} ^ {\prime \Psi} (W, \psi) = \operatorname{drop} _ {U} W, \\ \operatorname{copy} _ {U} ^ {\prime \Psi} (V, \varphi) = \operatorname{copy} _ {U} (V, \pi_ {2} \circ \varphi). \\ \end{array}
\]

Proof. Pick \((V,\varphi)\in \mathcal{V} / (\Psi \ltimes \mathbf{y}U)\). Then \(\varphi\) factors as \((\psi^{W_0\Rightarrow \Psi}\ltimes \mathbf{y}U)\circ \varphi_0^{V\to W_0\times U}\). Then \((V,\varphi_0)\in \mathcal{V} / (W_0\times U)\) and hence \(\exists_U^{W_0}(V,\varphi_0)\in \mathcal{W} / W_0\). We define

\[
\begin{array}{l} \exists_ {U} ^ {\prime \Psi} (V, \varphi) := \Sigma^ {\prime \psi} \exists_ {U} ^ {\prime W _ {0}} (V, \varphi_ {0}) \\ = \Sigma^ {\prime \psi} (\exists_ {U} (V, \pi_ {2} \circ \varphi_ {0}), \mathsf {d r o p} _ {U} \circ \exists_ {U} \varphi_ {0}) \\ = \left(\exists_ {U} \left(V, \pi_ {2} ^ {W _ {0} \ltimes U \rightarrow U} \circ \varphi_ {0}\right), \psi \circ \operatorname{drop} _ {U} \circ \exists_ {U} \varphi_ {0}\right) \\ = \left(\exists_ {U} \left(V, \pi_ {2} ^ {\Psi \ltimes \mathbf {y} U \rightarrow \mathbf {y} U} \circ \varphi\right), \psi \circ \operatorname{drop} _ {U} \circ \exists_ {U} \varphi_ {0}\right). \\ \end{array}
\]

We need to prove that this is well-defined, i.e. respects equality on the co-end that defines \( V \Rightarrow \Psi \ltimes \mathbf{y}U \). To this end, assume that \( \varphi = (\psi_0^{W_0 \Rightarrow \Psi} \ltimes \mathbf{y}U) \circ \varphi_0^{V \to W_0 \ltimes U} = (\psi_1^{W_1 \Rightarrow \Psi} \ltimes \mathbf{y}U) \circ \varphi_1^{V \to W_1 \ltimes U} \). This means there are a zigzag \( \zeta \) from \( W_0 \) to \( W_1 \), jagwise morphisms \( V \to \zeta \ltimes U \) and jagwise cells \( \zeta \Rightarrow \Psi \) such that the following triangles commute:

![img-15.jpeg](img-15.jpeg)

By naturality of \(\pi_2\), we find that \((V, \pi_2 \circ \varphi_0) = (V, \pi_2 \circ \varphi_1) \in \mathcal{V} / U\). By naturality of \(\mathrm{drop}_U\), we find that \(\psi_0 \circ \mathrm{drop}_U \circ \exists_U \varphi_0 = \psi_1 \circ \mathrm{drop}_U \circ \exists_U \varphi_1: (V, \pi_2 \circ \varphi_0) = (V, \pi_2 \circ \varphi_1) \Rightarrow \Psi\). We conclude that \(\exists_U^{/\Psi}(V, \varphi)\) is well-defined.

To prove adjointness, we first show how \(\exists_U^{\prime \Psi}\) on the right can be turned into \(\exists_U^{\prime \Psi}\) on the left. Pick a morphism \(\chi : (V, \varphi) \to \exists_U^{\prime \Psi}(W, \psi) = (W \ltimes U, \psi \ltimes \mathbf{y}U)\) in \(\mathcal{V}/(\Psi \ltimes \mathbf{y}U)\). Then one representation of \(\varphi\) is \(\varphi = (\psi \ltimes \mathbf{y}U) \circ \chi\) so by definition, \(\exists_U^{\prime \Psi}(V, \varphi) = (\exists_U(V, \pi_2 \circ \varphi), \psi \circ \mathrm{drop}_U \circ \exists_U \chi)\) which clearly factors over \(\psi\), i.e. has a morphism \(\mathrm{drop}_U \circ \exists_U \chi : \exists_U^{\prime \Psi}(V, \varphi) \to (W, \psi)\). If \(\chi = \mathrm{id}\), then we obtain the co-unit \(\mathrm{drop}_U^{\prime \Psi} = \mathrm{drop}_U \circ \exists_U \mathrm{id} = \mathrm{drop}_U\).

28

Next, we construct the unit $\mathsf{copy}_U^{/\Psi} : (V, \varphi) \to \mathbb{J}_U^{/\Psi} \exists_U^{/\Psi}(V, \varphi)$. If $\varphi = (\psi \ltimes \mathbf{y}U) \circ \varphi_0$, then we have

$$\begin{array}{l} \mathbb{J}_U^{/\Psi} \exists_U^{/\Psi}(V, \varphi) = \mathbb{J}_U^{/\Psi} \Sigma^{/\psi} \exists_U^{/W_0}(V, \varphi_0) \\ = \Sigma^{/\psi \ltimes \mathbf{y}U} \mathbb{J}_U^{/W_0} \exists_U^{/W_0}(V, \varphi_0). \end{array}$$

On the other hand, $(V, \varphi) = \Sigma^{/\psi \ltimes \mathbf{y}U}(V, \varphi_0)$, so as the unit we can take $\mathsf{copy}_U^{/\Psi} = \Sigma^{/\psi \ltimes \mathbf{y}U} \mathsf{copy}_U^{/W_0} = \mathsf{copy}_U^{/W_0} = \mathsf{copy}_U$.

The adjunction laws are then inherited from $\exists_U \dashv \mathbb{J}_U$.

**Proposition 4.1.10** (Functoriality of the category of elements). A morphism of multipliers $\sqcup \ltimes \upsilon : \sqcup \ltimes U \to \sqcup \ltimes U'$ gives rise to a natural transformation $\Sigma^{/\Psi \ltimes \mathbf{y}\upsilon} \circ \mathbb{J}_U^{/\Psi} \to \mathbb{J}_{U'}^{/\Psi}$. Hence, if both multipliers are $\top$-slice right adjoint, we also get $\exists_U^{/\Psi} \circ \Sigma^{/\Psi \ltimes \mathbf{y}\upsilon} \to \exists_U^{/\Psi}$.

*Proof.* For any $(W, \psi) \in \mathcal{W}/\Psi$, we have to prove $(W \ltimes U, (\Psi \ltimes \mathbf{y}\upsilon) \circ (\psi \ltimes \mathbf{y}U)) \to (W \ltimes U', \psi \ltimes \mathbf{y}U')$. The morphism $W \ltimes \upsilon : W \ltimes U \to W \ltimes U'$ does the job. The second statement follows from lemma 2.1.1.

**Theorem 4.1.11** (Presheafwise quantification theorem). If $\sqcup \ltimes U$ is

1. $\top$-slice (or equivalently presheafwise) fully faithful and right adjoint, then we have a natural isomorphism $\mathsf{drop}_U^{/\Psi} : \exists_U^{/\Psi} \mathbb{J}_U^{/\Psi} \cong \mathsf{Id}$.
2. copointed, then we have

(a) $\mathsf{hide}_U^{/\Psi} : \Sigma_U^{/\Psi} \to \exists_U^{/\Psi}$ (if $\top$-slice, or equivalently presheafwise, right adjoint),
(b) $\mathsf{spoil}_U^{/\Psi} : \mathbb{J}_U^{/\Psi} \to \Omega_U^{/\Psi}$ (if $\Omega_U^{/\Psi}$ exists),
(c) in any case $\Sigma_U^{/\Psi} \mathbb{J}_U^{/\Psi} \to \mathsf{Id}$.

3. a comonad, then there is a natural transformation $\Sigma^{/\Psi \ltimes \mathbf{y}\delta} \circ \mathbb{J}_U^{/\Psi} \to \mathbb{J}_{U \ltimes U}^{/\Psi}$.
4. cartesian, then we have natural isomorphisms:

(a) $\exists_U^{/\Psi}(V, \varphi) \cong \Sigma_U^{/\Psi}(V, \varphi) = (V, \pi_1 \circ \varphi)$,
(b) $\mathbb{J}_U^{/\Psi}(W, \psi) \cong \Omega_U^{/\Psi}(W, \psi)$,
(c) $\exists_U^{/\Psi} \mathbb{J}_U^{/\Psi}(W, \psi) \cong \Sigma_U^{/\Psi} \Omega_U^{/\Psi}(W, \psi) \cong (W \times \mathbf{y}U, \psi \circ \pi_1)$.

Moreover, these isomorphisms become equality if $\exists_U^{/\Psi}$ is constructed as above from $\exists_U^{/W_0} = \Sigma_U^{/W_0}$, and $\Omega_U^{/\Psi}(W, \psi)$ is chosen wisely. (Both functors are defined only up to isomorphism.)

*Proof.* 1. This is a standard fact about fully faithful right adjoints such as $\mathbb{J}_U^{/\Psi}$.

2. By lemma 2.1.1, it is sufficient to prove $\Sigma_U^{/\Psi} \mathbb{J}_U^{/\Psi} \to \mathsf{Id}$, and indeed we have $\pi_1 : \Sigma_U^{/\Psi} \mathbb{J}_U^{/\Psi}(W, \psi) = (W \ltimes U, \pi_1 \circ (\psi \ltimes \mathbf{y}U)) = (W \ltimes U, \psi \circ \pi_1) \to (W, \psi)$.
3. This is a special case of proposition 4.1.10.
4. (a) Let $\varphi = (\psi \ltimes \mathbf{y}U) \circ \varphi_0$. Then we have

$$\exists_U^{/\Psi}(V, \varphi) = \Sigma^{/\psi} \exists_U^{/W_0}(V, \varphi_0)$$

$$\cong \Sigma^{/\psi} \Sigma_U^{/W_0}(V, \varphi_0)$$

$$= \Sigma^{/\psi}(V, \pi_1 \circ \varphi_0)$$

$$= (V, \psi \circ \pi_1 \circ \varphi_0) = (V, \pi_1 \circ (\psi \ltimes \mathbf{y}U) \circ \varphi_0) = (V, \pi_1 \circ \varphi).$$

(b) This follows from the definitions.

29

(c) We have

\[
\exists_ {U} ^ {\prime \Psi} \exists_ {U} ^ {\prime \Psi} (W, \psi) = \exists_ {U} ^ {\prime \Psi} (W \times U, \psi \times \mathbf {y} U) \cong (W \times U, \pi_ {1} \circ (\psi \times \mathbf {y} U)) \tag {36}
\]

and of course \(\pi_1\circ (\psi \times \mathbf{y}U) = \psi \circ \pi_1:W\times U\to \Psi\)

Theorem 4.1.12 (Presheafwise quotient theorem \( ^{§A} \) ). If  \( \sqcup \times U : W \to V \)  is T-slice (or equivalently presheafwise, for either notion of shard-freedom) fully faithful and shard-free, then

1. (Obsolete.) \(\exists_{U}^{\prime \Psi}:\mathcal{W} / \Psi \simeq (\mathcal{V} / / U) / (\Psi \ltimes \mathbf{y}U,\pi_2)\) is an equivalence of categories.\(^{15}\)
2. \(\exists_{U}^{\prime \Psi}:\mathcal{W} / \Psi \simeq \mathcal{V} / / (\Psi \ltimes \mathbf{y}U)\) is an equivalence of categories.

### 4.2 Acting on presheaves

Proposition 4.2.1. The functor \(\sqcup \ltimes \mathbf{y}U:\widehat{\mathcal{W}}\to \widehat{\mathcal{V}}\)

1. is a multiplier for yU,
2. has the property that \(\exists_{\mathbf{y}U}:\widehat{\mathcal{W}}\to \widehat{\mathcal{V}} /\mathbf{y}U\) is naturally isomorphic to \((\exists_U)_{!}:\widehat{\mathcal{W}}\to \widehat{\mathcal{V} / U}\) over the equivalence between their codomains,
3. has the property that the slice functor \(\exists_{\mathbf{y}U}^{\prime \Psi}:\widehat{\mathcal{W}} /\Psi \to \widehat{\mathcal{V}} /\big(\Psi \ltimes \mathbf{y}U\big)\) is naturally isomorphic to the left lifting of the elements functor \((\exists_U^{\prime \Psi})_{!}:\widehat{\mathcal{W} / \Psi}\to \widehat{\mathcal{V} / (\Psi\ltimes\mathbf{y}U)}\) over the equivalences between their domains and codomains,
4. is copointed if and only if \(\sqcup \ltimes U\) is,
5. is a comonad if and only if \(\sqcup \ltimes U\) is,
6. is cartesian if and only if \(\sqcup \ltimes U\) is,
7. is \(\top\)-slice fully faithful if and only if \(\sqcup \ltimes U\) is \(\top\)-slice fully faithful,
8. is slicewise fully faithful if and only if \(\sqcup \ltimes U\) is presheafwise fully faithful,
9. is \(\top\)-slice right adjoint if \(\sqcup \ltimes U\) is \(\top\)-slice right adjoint, and

- \(\exists_{\mathbf{y}U}\) is naturally isomorphic to \((\exists_U)_!\) over the equivalence \(\widehat{\mathcal{V}/U} \simeq \widehat{\mathcal{V}}/\mathbf{y}U\),
- \(\exists_{\mathbf{y}U}^{\prime \Psi}\) is naturally isomorphic to \((\exists_U^{\prime \Psi})_!\) over the equivalences between their domain and codomain.

Proof. 1. Since \(\top \ltimes \mathbf{y}U \cong \mathbf{y}\top \ltimes \mathbf{y}U \cong \mathbf{y}(\top \ltimes U) \cong \mathbf{y}U\). We use, in order, that \(\mathbf{y}\) preserves the terminal object, that \(F_{!}\circ \mathbf{y} \cong \mathbf{y}\circ F\) (theorem 2.3.2) and that \(\sqcup \ltimes U\) is a multiplier for \(U\).

2. The functor \((\exists_U)_{!}\) sends a presheaf \(\Gamma \in \widehat{\mathcal{W}}\) to the presheaf in \(\widehat{\mathcal{V} / U}\) determined by

\[
(V, \varphi) \Rightarrow (\exists_ {U}) _ {!} \Gamma = \exists W. ((V, \varphi) \rightarrow \exists_ {U} W) \times (W \Rightarrow \Gamma). \tag {37}
\]

On the other hand, \(\exists_{\mathbf{y}U}\Gamma\) is the slice object \((\Gamma \ltimes \mathbf{y}U,\pi_2)\in \widehat{\mathcal{V}} /\mathbf{y}U\). Taking the preimage of \(\pi_2\) (proposition 2.3.6), we get a presheaf \(\Delta \in \widehat{\mathcal{V} / U}\) determined by

\[
\begin{array}{l} (V, \varphi) \Rightarrow \Delta = \left\{\left(\gamma \ltimes \mathbf {y} U\right) \circ \chi : V \Rightarrow \Gamma \ltimes \mathbf {y} U \mid \pi_ {2} \circ (\gamma \ltimes \mathbf {y} U) \circ \chi = \varphi \right\} \\ = \left\{\left(\gamma \ltimes \mathbf {y} U\right) \circ \chi : V \Rightarrow \Gamma \ltimes \mathbf {y} U \mid \pi_ {2} \circ \chi = \varphi \right\} \\ \cong \exists W. (\chi : V \to W \ltimes U) \times (\gamma : W \Rightarrow \Gamma) \times (\pi_ {2} \circ \chi = \varphi) \\ \cong \exists W. (\chi : (V, \varphi) \to \exists_ {U} W) \times (W \Rightarrow \Gamma). \\ \end{array}
\]

Indeed, we see that these functors are isomorphic.

\( ^{15} \) We use a slight abuse of notation as  \( (\mathcal{V}//U)/(\Psi \ltimes \mathbf{y}U, \pi_{2}) \)  is in fact neither a slice category nor a category of elements.

30

3. The functor $(\exists_U^{\prime \Psi})_1$ sends a presheaf $\Psi \mid \Gamma \vdash \mathrm{Ctx}$ over $\mathcal{W} / \Psi$ to the presheaf $\Psi \ltimes \mathbf{y}U \mid (\exists_U \Psi)_1 \Gamma \vdash \mathrm{Ctx}$ over $\mathcal{V} / (\Psi \ltimes \mathbf{y}U)$ determined by:

$$
(V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y}U}) \Rightarrow \left(\exists_U^{\prime \Psi}\right)_1 \Gamma = \exists (W, \psi^{W \Rightarrow \Psi}). ((V, \varphi) \rightarrow \exists_U^{\prime \Psi}(W, \psi)) \times ((W, \psi) \Rightarrow \Gamma). \tag{38}
$$

On the other hand, $\exists_{\mathbf{y}U}^{\prime \Psi}(\Psi \Gamma, \pi)$ is the slice $(\Psi \Gamma \ltimes \mathbf{y}U, \pi \ltimes \mathbf{y}U) \in \widehat{\mathcal{V}} / (\Psi \ltimes \mathbf{y}U)$. Taking the preimage of $\pi \ltimes \mathbf{y}U$ (proposition 2.3.6), we get a presheaf $\Psi \ltimes \mathbf{y}U \mid \Delta \vdash \mathrm{Ctx}$ over $\mathcal{V} / (\Psi \ltimes \mathbf{y}U)$ determined by

$$
\begin{array}{l}
(V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y}U}) \Rightarrow \Delta \\
= \{(\psi \cdot \gamma \ltimes \mathbf{y}U) \circ \chi : V \Rightarrow \Psi \cdot \Gamma \ltimes \mathbf{y}U \mid (\pi \ltimes \mathbf{y}U) \circ (\psi \cdot \gamma \ltimes \mathbf{y}U) \circ \chi = \varphi\} \\
= \{(\psi \cdot \gamma \ltimes \mathbf{y}U) \circ \chi : V \Rightarrow \Psi \cdot \Gamma \ltimes \mathbf{y}U \mid (\psi \ltimes \mathbf{y}U) \circ \chi = \varphi\} \\
\cong \exists W. (\chi : V \rightarrow W \ltimes U) \times (\psi : W \Rightarrow \Psi) \times (\gamma : (W, \psi) \Rightarrow \Gamma) \times ((\psi \ltimes \mathbf{y}U) \circ \chi = \varphi) \\
\cong \exists (W, \psi^{W \Rightarrow \Psi}). (\chi : (V, \varphi) \rightarrow \exists_U^{\prime \Psi}(W, \psi)) \times (\gamma : (W, \psi) \Rightarrow \Gamma).
\end{array}
$$

Indeed, we see that these functors are isomorphic.

4. Assume that $\sqcup \ltimes U$ is copointed. It is immediate from the construction of $\sqcup_1$ that $\sqcup_1$ preserves natural transformations. Moreover, we have $\mathrm{Id}_1 \cong \mathrm{Id}$, so we get $\pi_1 : (\sqcup \ltimes \mathbf{y}U) \rightarrow \mathrm{Id}$.

Conversely, assume that $\sqcup \ltimes \mathbf{y}U$ is copointed. Then we have $\mathbf{y}(\sqcup \ltimes U) \cong (\mathbf{y} \sqcup \ltimes \mathbf{y}U) \rightarrow \mathbf{y}$. Since $\mathbf{y}$ is fully faithful, we have proven $(\sqcup \ltimes U) \rightarrow \mathrm{Id}$.

5. Analogous to the previous point.

6. Assume that $\sqcup \ltimes U$ is cartesian. We apply the universal property of the cartesian product, and the co-Yoneda lemma:

$$
\begin{array}{l}
V \Rightarrow (\Gamma \ltimes \mathbf{y}U) = \exists W. (V \rightarrow W \ltimes U) \times (W \Rightarrow \Gamma) \\
\cong \exists W. (V \rightarrow W) \times (V \rightarrow U) \times (W \Rightarrow \Gamma) \\
\cong (V \rightarrow U) \times (V \Rightarrow \Gamma) \\
\cong (V \Rightarrow \mathbf{y}U) \times (V \Rightarrow \Gamma).
\end{array}
$$

Conversely, if $\sqcup \ltimes \mathbf{y}U$ is cartesian, we have

$$
\begin{array}{l}
V \rightarrow W \ltimes U = V \Rightarrow \mathbf{y}(W \ltimes U) \\
\cong V \Rightarrow \mathbf{y}W \ltimes \mathbf{y}U \\
\cong (V \Rightarrow \mathbf{y}W) \times (V \Rightarrow \mathbf{y}U) \\
\cong (V \rightarrow W) \times (V \rightarrow U).
\end{array}
$$

7. This follows from point 2 and proposition 2.3.4.

8. This follows from point 3 and proposition 2.3.4.

9. • We know that $(\exists_U)_1 \dashv (\exists_U)_1$ so moving it through the natural isomorphism yields a left adjoint to $\exists_{\mathbf{y}U}$.

• By proposition 4.1.9, $\exists_U^{\prime \Psi}$ exists. We know that $(\exists_U^{\prime \Psi})_1 \dashv (\exists_U^{\prime \Psi})_1$ so moving it through the natural isomorphism yields a left adjoint to $\exists_{\mathbf{y}U}^{\prime \Psi}$.

31

### 4.3 Four adjoint functors

Unlike the slice category \(\widehat{\mathcal{W}} / \Psi\), the equivalent category \(\widehat{\mathcal{W} / \Psi}\) is a presheaf category and therefore immediately a model of dependent type theory. Therefore, we prefer to work with that category, and to use the corresponding functors:

Definition 4.3.1. The adjoint functors \(\exists_{U}^{\prime \Psi}\dashv \exists_{U}^{\prime \Psi}\) give rise to four adjoint functors between presheaf categories over slice categories, which we denote

\[
\exists_ {\mathbf {y} U} ^ {\Psi |} \dashv \exists_ {\mathbf {y} U} ^ {\Psi |} \dashv \forall_ {\mathbf {y} U} ^ {\Psi |} \dashv \delta_ {\mathbf {y} U} ^ {\Psi |}. \tag {39}
\]

We call the fourth functor transpension.

The units and co-units will be denoted:

\[
\begin{array}{l} \operatorname{copy} _ {\mathbf {y} U} ^ {\Psi |}: \quad \operatorname{Id} \rightarrow \exists_ {\mathbf {y} U} ^ {\Psi |} \exists_ {\mathbf {y} U} ^ {\Psi |} \\ \operatorname{const} _ {\mathbf {y} U} ^ {\Psi |}: \quad \operatorname{Id} \rightarrow \forall_ {\mathbf {y} U} ^ {\Psi |} \exists_ {\mathbf {y} U} ^ {\Psi |} \\ \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |}: \quad \operatorname{Id} \rightarrow \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} \\ \operatorname{drop} _ {\mathbf {y} U} ^ {\Psi |}: \exists_ {\mathbf {y} U} ^ {\Psi |} \exists_ {\mathbf {y} U} ^ {\Psi |} \rightarrow \operatorname{Id} \\ \operatorname{app} _ {\mathbf {y} U} ^ {\Psi |}: \quad \exists_ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} \rightarrow \operatorname{Id} \\ \operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}: \quad \forall_ {\mathbf {y} U} ^ {\Psi |} \delta_ {\mathbf {y} U} ^ {\Psi |} \rightarrow \operatorname{Id} \\ \end{array}
\]

For now, we define all of these functors only up to isomorphism, i.e. for the middle two we do not specify whether they arise as a left, central or right lifting.

Note that, if in a judgement \(\Psi \mid \Gamma \vdash J\), we view the part before the pipe (|) as part of the context, then \(\exists_{\mathbf{y}U}^{\Gamma |}\) and \(\forall_{\mathbf{y}U}^{\Gamma |}\) bind a (substructural) variable of type \(\mathbf{y}U\), whereas \(\exists_{\mathbf{y}U}^{\Gamma |}\) and \(\delta_{\mathbf{y}U}^{\Gamma |}\) depend on one.

It is worth mentioning that, since \(\sqcup \ltimes U = \Sigma_U \exists_U\), the functors in definition 4.0.1 can be (essentially) retrieved as

\[
\sqcup \ltimes \mathbf {y} U = \Sigma_ {\mathbf {y} U} ^ {\top |} \exists_ {\mathbf {y} U} ^ {\top |} \quad \dashv \quad \mathbf {y} U \rightharpoonup \sqcup = \forall_ {\mathbf {y} U} ^ {\top |} \Omega_ {\mathbf {y} U} ^ {\top |} \quad \dashv \quad \mathbf {y} U \vee \sqcup = \Pi_ {\mathbf {y} U} ^ {\top |} \delta_ {\mathbf {y} U} ^ {\top |}. \tag {41}
\]

Corollary 4.3.2. The properties asserted by proposition 4.2.1 for \(\exists_{\mathbf{y}U}^{\prime \Psi}\) also hold for \(\exists_{\mathbf{y}U}^{\Psi}\).

Proof. Follows from the fact that \(\exists_{\mathbf{y}U}^{\Psi} \cong (\exists_{U}^{\prime \Psi})_{1}\), and the observation in proposition 4.2.1 that this functor in turn corresponds to \(\exists_{\mathbf{y}U}^{\prime \Psi}\).

Proposition 4.3.3 (Presheaf functoriality). A morphism of multipliers \(\sqcup \ltimes v: \sqcup \ltimes U \to \sqcup \ltimes U'\) gives rise to natural transformations

- \(\exists_{\mathbf{y}U'}^{\Psi|} \circ \Sigma^{\Psi \ltimes \mathbf{y}v|} \to \exists_{\mathbf{y}U'}^{\Psi}\) (if \(\top\)-slice (hence presheafwise) right-adjoint),
•  \( \Sigma^{\Psi\ltimes\mathbf{y}v|}\circ\exists_{\mathbf{y}U}^{\Psi|}\to\exists_{\mathbf{y}U'}^{\Psi|} \)  and  \( \exists_{\mathbf{y}U}^{\Psi|}\to\Omega^{\Psi\ltimes\mathbf{y}v|}\circ\exists_{\mathbf{y}U'}^{\Psi|} \) ,
•  \( \forall_{yU'}^{\Psi|}\to\forall_{yU'}^{\Psi|}\circ\Omega^{\Psi\ltimes yv|} \)  and  \( \forall_{yU'}^{\Psi|}\circ\Pi^{\Psi\ltimes yv|}\to\forall_{yU'}^{\Psi|} \) ,
•  \( \Pi^{\Psi\ltimes\mathbf{y}v|}\circ\delta_{\mathbf{y}U}^{\Psi|}\to\delta_{\mathbf{y}U'}^{\Psi|} \)

Proof. Follows directly from proposition 4.1.10.

Proposition 4.3.4 (Contextual quantification theorem). If \(\sqcup \ltimes U\) is

1. \(\top\)-slice (or equivalently presheafwise) fully faithful, then \(\mathrm{drop}_{\mathbf{y}U}^{\Psi|}\) (if \(\top\)-slice right adjoint), \(\mathrm{const}_{\mathbf{y}U}^{\Psi|}\) and \(\mathrm{unmerid}_{\mathbf{y}U}^{\Psi|}\) are natural isomorphisms.
2. copointed, then we have

(a)  \( \operatorname{hide}_{\mathbf{y}U}^{\Psi|}:\Sigma_{\mathbf{y}U}^{\Psi|}\to\exists_{\mathbf{y}U}^{\Psi|} \)  (if  \( \top \) -slice, or equivalently presheafwise, right adjoint),

(b)  \( \operatorname{spoil}_{\mathbf{y}U}^{\Psi|}:\exists_{\mathbf{y}U}^{\Psi|}\to\Omega_{\mathbf{y}U}^{\Psi|} \)

32

(c) $\text{cospoil}_{\mathbf{y}U}^{\Psi|}: \Pi_{\mathbf{y}U}^{\Psi|} \to \forall_{\mathbf{y}U}^{\Psi|}$.

3. a comonad, then we can apply proposition 4.3.3 to $\sqcup \ltimes \delta: \sqcup \ltimes U \to \sqcup \ltimes (U \ltimes U)$.
4. cartesian, then we have natural isomorphisms:

(a) $\exists_{\mathbf{y}U}^{\Psi|} \cong \Sigma_{\mathbf{y}U}^{\Psi|}$,
(b) $\exists_{\mathbf{y}U}^{\Psi|} \cong \Omega_{\mathbf{y}U}^{\Psi|}$,
(c) $\forall_{\mathbf{y}U}^{\Psi|} \cong \Pi_{\mathbf{y}U}^{\Psi|}$,
(d) $\emptyset_{\mathbf{y}U}^{\Psi|} \cong \$$\mathbf{\$}_{\mathbf{y}U}^{\Psi|}$ (if $\Omega_U^{\Psi}$ exists).

Equality is achieved for any pair of functors if they are lifted in the same way from functors that were equal in theorem 4.1.11.

Proof. 1. This is a standard fact about fully faithful left/right adjoints.

2. By lemma 2.1.1, it is sufficient to prove $\Sigma_{\mathbf{y}U}^{\Psi|} \exists_{\mathbf{y}U}^{\Psi|} \to \text{Id}$, which follows immediately from $\pi_1: \Sigma_U^{\Psi} \exists_U^{\Psi} \to \text{Id}$.
3. Of course we can.
4. This is an immediate corollary of theorem 4.1.11.

Proposition 4.3.5 (Fresh exchange). If $\Psi \mid \Gamma \vdash \text{Ctx}$, i.e. $\Gamma \in \widehat{\mathcal{W}/\Psi}$, then we have an isomorphism of slice objects (natural in $\Gamma$):

$$(\Psi \ltimes \mathbf{y}U) \xrightarrow{\exists_{\mathbf{y}U}^{\Psi|}} \Gamma \xrightarrow{\cong} \Psi \cdot \Gamma \ltimes \mathbf{y}U \quad \begin{array}{c} \pi \\ \downarrow \\ \pi \ltimes \mathbf{y}U. \end{array} \quad \begin{array}{c} \pi \ltimes \mathbf{y}U \end{array} \tag{42}$$

This proposition explains the meaning of $\exists_{\mathbf{y}U}^{\Gamma}$: it is the type depending on a variable of type $\mathbf{y}U$ whose elements are required to be fresh for that variable, where the meaning of 'fresh' depends on the nature of the multiplier. If the multiplier is cartesian, then $\exists_{\mathbf{y}U}^{\Gamma}$ is clearly just weakening over $\mathbf{y}U$.

Proof. The slice object on the right is $\exists_{\mathbf{y}U}^{\Psi|}(\Psi \cdot \Gamma, \pi)$. By proposition 4.2.1, this is isomorphic to $\exists_{\mathbf{y}U}^{\Psi|}\Gamma$ over the equivalence from proposition 2.3.6 which sends $\Delta$ to $((\Psi \ltimes \mathbf{y}U) \cdot \Delta, \pi)$.

### 4.4 Investigating the transpension functor

Definition 4.4.1. 1. We define the indirect boundary $\Psi \ltimes \partial U$ as the pullback

$$\begin{array}{c} \Psi \ltimes \partial U \xrightarrow{\subseteq} \Psi \ltimes \mathbf{y}U \\ \downarrow \pi_2 \\ \partial U \xrightarrow{\subseteq} \mathbf{y}U, \end{array} \tag{43}$$

i.e. the subpresheaf of $\Psi \ltimes \mathbf{y}U$ consisting of all cells $\varphi$ such that $\pi_2 \circ \varphi$ is not dimensionally split.

2. We define the direct boundary, also denoted $\Psi \ltimes \partial U$, as the subpresheaf of $\Psi \ltimes \mathbf{y}U$ consisting of all cells $\varphi$ that are not directly dimensionally split.

By proposition 3.5.3, the indirect boundary is a subpresheaf of the direct boundary.

33

**Remark 4.4.2.** Just like $\top$-slice shard-freedom (remark 3.4.19), direct presheafwise shard-freedom can be formulated using (co)sieves. A multiplier is directly presheafwise shard-free if either of the following equivalent criteria is satisfied:

- The objects in the essential image of $\exists_U^{\exists / \Xi}$ constitute a cosieve in $\mathcal{W} / \Xi \ltimes \mathbf{y} U$.
- The objects *outside* the essential image of $\exists_U^{\exists / \Xi}$ constitute a sieve in $\mathcal{W} / \Xi \ltimes \mathbf{y} U$.

The objects of the cosieve generated by objects of the essential image of $\exists_U^{\exists / \Xi}$, are called directly dimensionally split. The boundary $\Xi \ltimes \partial U$ is the largest sieve in $\mathcal{W} / \Xi \ltimes \mathbf{y} U$ (largest subpresheaf of $\Xi \ltimes \mathbf{y} U$) that is disjoint with the objects of the essential image of $\exists_U^{\exists / \Xi}$.

If $\sqcup \ltimes U$ is presheafwise fully faithful, then the above conditions are furthermore equivalent to $\exists_U^{\exists / \Xi}$ being a Street opfibration.

**Definition 4.4.3.** For either notion of boundary, write $(\in \partial U)$ for the inverse image of $\Psi \ltimes \partial U \subseteq \Psi \ltimes \mathbf{y} U$, which is a presheaf over $\mathcal{W} / (\Psi \ltimes \mathbf{y} U)$ such that $(\Psi \ltimes \mathbf{y} U) \cdot (\in \partial U) \cong \Psi \ltimes \partial U$. We also write $(\in \partial U)$ for the inverse image of $\partial U \subseteq \mathbf{y} U$. Finally, we write $\Sigma_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U} \dashv \dots$ for the functors arising from $\Psi \ltimes \partial U \subseteq \Psi \ltimes \mathbf{y} U$.

**Theorem 4.4.4** (Poles of the transpension). For either notion of boundary and any multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$, the functor $\Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U} \circ \delta_{\mathbf{y} U}^{\Psi} : \widehat{\mathcal{W} / \Psi} \to \widehat{\mathcal{V} / (\Psi \ltimes \partial U)}$ sends any presheaf to the terminal presheaf, i.e. $\Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U} \circ \delta_{\mathbf{y} U}^{\Psi} = \top$.

*Proof.* We show that there is always a unique cell $(V, \varphi^{V \Rightarrow \Psi \ltimes \partial U}) \Rightarrow \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U} \delta_{\mathbf{y} U}^{\Psi} \Gamma$. We have

$$\begin{aligned} & (V, \varphi^{V \Rightarrow \Psi \ltimes \partial U}) \Rightarrow \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U} \delta_{\mathbf{y} U}^{\Psi} \Gamma \\ &= \Sigma_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U} (V, \varphi^{V \Rightarrow \Psi \ltimes \partial U}) \Rightarrow \delta_{\mathbf{y} U}^{\Psi} \Gamma \\ &= (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \Rightarrow \delta_{\mathbf{y} U}^{\Psi} \Gamma \\ &= \forall_{\mathbf{y} U}^{\Psi} \mathbf{y} (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \to \Gamma \\ &= \forall (W, \psi^{W \Rightarrow \Psi}) \cdot \Big( (W, \psi) \Rightarrow \forall_{\mathbf{y} U}^{\Psi} \mathbf{y} (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \Big) \to ((W, \psi) \Rightarrow \Gamma) \\ &= \forall (W, \psi^{W \Rightarrow \Psi}) \cdot \Big( \exists_U^{\Psi} (W, \psi) \Rightarrow \mathbf{y} (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \Big) \to ((W, \psi) \Rightarrow \Gamma) \\ &= \forall (W, \psi^{W \Rightarrow \Psi}) \cdot \big( (W \ltimes U, \psi \ltimes \mathbf{y} U) \to (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \big) \to ((W, \psi) \Rightarrow \Gamma) \end{aligned}$$

and then we see that the last argument $\chi$ cannot exist. Indeed, suppose we have a commuting diagram (where the dotted part only applies in the indirect setting)

$$\begin{array}{c} W \ltimes U \xrightarrow{\chi} V \\ \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \quad \downarrow \\ \pi \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \tag{44}$$

**indirect boundary** Then we see that $\pi_2 \circ \varphi : V \to U$ is dimensionally split with section $\chi$ but is also a cell of $\partial U$ which means exactly that it is not dimensionally split.

**direct boundary** Then we see that $\varphi : V \Rightarrow \Psi \ltimes \mathbf{y} U$ is directly dimensionally split with section $\chi$ but it is also a cell of $\Psi \ltimes \partial U$ which means exactly that it is not directly dimensionally split. $\square$

34

The following theorem shows that dimensionally split morphisms are an interesting concept:

**Theorem 4.4.5** (Boundary theorem). 1. (Obsolete.) Using the indirect boundary, we have

$$\top \ltimes \mathbf{y} U \mid (\in \partial U) \cong \mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot \vdash \mathsf{Ctx}$$

and more generally

$$\Psi \ltimes \mathbf{y} U \mid (\in \partial U) \cong \Omega^{( ) \ltimes \mathbf{y} U \mid} \mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot \vdash \mathsf{Ctx}.$$

2. Using the direct boundary, we have

$$\Psi \ltimes \mathbf{y} U \mid (\in \partial U) \cong \mathbb{Q}_{\mathbf{y} U}^{\Psi \mid} \bot \vdash \mathsf{Ctx}.$$

*Proof.* 1. We prove the first statement by characterizing the right hand side of the isomorphism. We have

$$\begin{aligned} & (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U}) \Rightarrow \mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot \\ & = \forall_{\mathbf{y} U}^{\top \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U}) \rightarrow \bot \\ & = \forall (W, ()^{W \Rightarrow \top}). ((W, ()) \Rightarrow \forall_{\mathbf{y} U}^{\top \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U})) \rightarrow ((W, ()) \Rightarrow \bot) \\ & = \forall (W, ()^{W \Rightarrow \top}). ((W, ()) \Rightarrow \forall_{\mathbf{y} U}^{\top \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & = \forall (W, ()^{W \Rightarrow \top}). (\exists_{U}^{\top} (W, ()) \rightarrow (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & = \forall (W, ()^{W \Rightarrow \top}). ((W \ltimes U, () \ltimes U) \rightarrow (V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & \cong \forall W. ((W \ltimes U, \pi_2) \rightarrow (V, \pi_2 \circ \varphi)) \rightarrow \varnothing \\ & \cong (\exists W. (W \ltimes U, \pi_2) \rightarrow (V, \pi_2 \circ \varphi)) \rightarrow \varnothing. \end{aligned}$$

Clearly, the left hand side of the last line is inhabited if and only if $\pi_2 \circ \varphi$ is dimensionally split. Hence, there is a unique cell $(V, \varphi^{V \Rightarrow \top \ltimes \mathbf{y} U}) \Rightarrow \mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot$ if and only if $\pi_2 \circ \varphi$ is *not* dimensionally split, showing that $\mathbb{Q}_{\mathbf{y} U}^{\top \mid} \bot$ is indeed isomorphic to $(\in \partial U)$.

The second statement follows from applying $\Omega^{( ) \ltimes \mathbf{y} U \mid}$ to both sides of the first statement and observing that, being defined by pullback, the indirect boundary predicate is preserved by the substitution functor.

2. We prove this by characterizing the right hand side of the isomorphism. We have

$$\begin{aligned} & (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \Rightarrow \mathbb{Q}_{\mathbf{y} U}^{\Psi \mid} \bot \\ & = \forall_{\mathbf{y} U}^{\Psi \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \rightarrow \bot \\ & = \forall (W, \psi^{W \Rightarrow \Psi}). ((W, \psi) \Rightarrow \forall_{\mathbf{y} U}^{\Psi \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow ((W, \psi) \Rightarrow \bot) \\ & = \forall (W, \psi^{W \Rightarrow \Psi}). ((W, \psi) \Rightarrow \forall_{\mathbf{y} U}^{\Psi \mid} \mathbf{y} (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & = \forall (W, \psi^{W \Rightarrow \Psi}). (\exists_{U}^{\top} (W, \psi) \rightarrow (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & = \forall (W, \psi^{W \Rightarrow \Psi}). ((W \ltimes U, \psi \ltimes U) \rightarrow (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow \varnothing \\ & \cong (\exists (W, \psi^{W \Rightarrow \Psi}). (W \ltimes U, \psi \ltimes U) \rightarrow (V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U})) \rightarrow \varnothing. \end{aligned}$$

Clearly, the left hand side of the last line is inhabited if and only if $\varphi$ is directly dimensionally split. Hence, there is a unique cell $(V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}) \Rightarrow \mathbb{Q}_{\mathbf{y} U}^{\Psi \mid} \bot$ if and only if $\varphi$ is *not* directly dimensionally split, showing that $\mathbb{Q}_{\mathbf{y} U}^{\Psi \mid} \bot$ is indeed isomorphic to $(\in \partial U)$. $\square$

**Remark 4.4.6.** In section 6.3 (theorem 6.3.1), we will see that unless the multiplier is $\top$-slice (or equivalently presheafwise) fully faithful, the transpension type may not be stable under substitution. Instead, for $\sigma : \Psi_1 \to \Psi_2$, we only have $\Omega^{\sigma \ltimes \mathbf{y} U \mid} \circ \mathbb{Q}_{\mathbf{y} U}^{\Psi_2 \mid} \to \mathbb{Q}_{\mathbf{y} U}^{\Psi_1 \mid} \circ \Omega^{\sigma \mid}$.

35

Instantiating this with $\sigma = () : \Psi \to \top$ and applying both hands to $\bot$, which is preserved by the substitution functor, we find $\Omega^{() \ltimes yU} \ldot{\lvert}_{yU} \bot \to \ldot{\lvert}_{yU}^{\Psi} \bot$, i.e. the indirect boundary predicate implies the direct boundary predicate.

Since the transpension type is stable under substitution for $\top$-slice (or equivalently presheafwise) fully faithful multipliers, we can conclude that for those multipliers, both notions of boundary coincide. In fact, we already proved this for $\top$-slice full multipliers (proposition 4.1.8).

**Theorem 4.4.7** (Transpension elimination). Let $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ be $\top$-slice (or equivalently presheafwise) fully faithful and shard-free. Then we have$^{16}$

$$
\begin{aligned}
\Psi \ltimes \mathbf{y}U \mid \Gamma \vdash \text{Ctx} \\
\Psi \mid \forall_{\mathbf{y}U}^{\Psi} \mid \Gamma \vdash A \text{ type} \\
\Psi \ltimes \mathbf{y}U \mid \Gamma \cdot \left\langle \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \mid A \right\rangle \vdash B \text{ type} \\
\Psi \ltimes \partial U \mid \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \mid \Gamma \vdash b_\partial : \left( \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \mid B \right) [(\text{id}, \bot)] \\
\Psi \mid \left( \forall_{\mathbf{y}U}^{\Psi} \mid \Gamma \right) \cdot A \vdash \dot{b} : \left( \forall_{\mathbf{y}U}^{\Psi} \mid B \right) \left[ \left( \pi, \left( \text{unmerid}_{\mathbf{y}U}^{\Psi} \right)^{-1} (\xi) \right) \right] \\
\Psi \ltimes \partial U \mid \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \left( \left( \forall_{\mathbf{y}U}^{\Psi} \mid \Gamma \right) \cdot A \right) \vdash^{\Omega_{(\in \partial U)}^{\Psi \ltimes \partial U}} \left( \text{app}_{\mathbf{y}U}^{\Psi} \left( \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \dot{b} \right) \right) = b_\partial \left[ \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \left( \text{app}_{\mathbf{y}U}^{\Psi} \circ \pi \right) \right] \\
: \left( \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \mid B \right) [(\text{id}, \bot)] \left[ \Omega_{(\in \partial U)}^{\Psi \ltimes \partial U} \left( \text{app}_{\mathbf{y}U}^{\Psi} \circ \pi \right) \right] \\
\hline
\end{aligned}
$$

and $b$ reduces to $b_\partial$ and $\dot{b}$ if we apply to it the same functors and substitutions that have been applied to $B$ in the types of $b_\partial$ and $\dot{b}$.

(If the multiplier is not $\top$-slice (or equivalently presheafwise) right adjoint, then $\lleftarrow_{\mathbf{y}U}^{\Psi}$ may not be a CwF morphism, but the term $\text{app}_{\mathbf{y}U}^{\Psi} \left( \lleftarrow_{\mathbf{y}U}^{\Psi} \dot{b} \right)$ is essentially a dependent transposition for the adjunction $\lleftarrow_{\mathbf{y}U}^{\Psi} \dashv \forall_{\mathbf{y}U}^{\Psi}$ which even exists if only the right adjoint is a CwF morphism [Nuy18]).

In words: if we want to eliminate an element of the transpension type, then we can do so by induction. We distinguish two cases and a coherence condition:

- In the first case ($b_\partial$), we are on the boundary of $U$ and the transpension type trivializes.
- In the second case, we are defining an action on cells that live over all of $\mathbf{y}U$. In the transpension type, such cells are in 1-1 correspondence with cells of type $A$ under the isomorphism $\text{unmerid}_{\mathbf{y}U}^{\Psi} : \forall_{\mathbf{y}U}^{\Psi} \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \cong \text{Id}$.
- The boundary of the image of cells in the second case, must always be $b_\partial$.

Note that right adjoint weak CwF morphisms such as $\ldot{\lvert}_{\mathbf{y}U}^{\Psi}$ give rise to a DRA by applying the CwF morphism and then substituting with the unit of the adjunction. As such, the transpension type is modelled by the DRA sending $A$ to $\left\langle \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \mid A \right\rangle = \left( \ldot{\lvert}_{\mathbf{y}U}^{\Psi} \mid A \right) \left[ \text{reid}_{\mathbf{y}U}^{\Psi} \right]$.

*Proof.* **Well-formedness.** We first show that the theorem is well-formed.

- The rule for $\Gamma$ just assumes that $\Gamma$ is a presheaf over $\mathcal{V}/(\Psi \ltimes \mathbf{y}U)$.
- Then $\forall_{\mathbf{y}U}^{\Psi} \mid \Gamma$ is a presheaf over $\mathcal{W}/\Psi$ and we assume that $A$ is a type in that context, i.e. a presheaf over the category of elements of $\forall_{\mathbf{y}U}^{\Psi} \mid \Gamma$.
- Then the DRA of $\ldot{\lvert}_{\mathbf{y}U}^{\Psi}$ applied to $A$ is a type in context $\Gamma$. We assume that $B$ is a type over the extended context.

$^{16}$regardless of the notion of boundary, as these coincide for $\top$-slice full multipliers (proposition 4.1.8); we do not even have to distinguish cases in the proof as we will simply apply the appropriate version of the quotient theorem 4.1.12.

36

- Being a central lifting, \(\Omega_{(\in \partial U)}^{\Psi \ltimes \partial U|}\) is a CwF morphism and can be applied to \(B\), yielding a type in context

\[
\begin{array}{l} \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \left(\Gamma . \left(\mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right) \left[ \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right]\right) = \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \Gamma . \left(\Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right) \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right] \\ \cong \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \partial U |} \Gamma . \top , \\ \end{array}
\]

where the isomorphism is an application of theorem 4.4.4. The substitution \((\mathrm{id},\_) = \pi^{-1}\) yields a type in context \(\Omega_{(\in \partial U)}^{\Psi \ltimes \partial U|}\Gamma\). We assume that \(b_{\partial}\) has this type.

- Being a central lifting, \(\forall_{\mathbf{y}U}^{\Psi|}\) is a CwF morphism and can be applied to \(B\), yielding a type in context

\[
\forall_ {\mathbf {y} U} ^ {\Psi |} \left(\Gamma . \left(\mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right) \left[ \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right]\right) = \forall_ {\mathbf {y} U} ^ {\Psi |} \Gamma . \left(\forall_ {\mathbf {y} U} ^ {\Psi |} \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right) \left[ \forall_ {\mathbf {y} U} ^ {\Psi |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right].
\]

The natural transformation \((\mathrm{unmerid}_{\mathbf{y}U}^{\Psi|})^{-1}\) gives rise [Nuy18] to a function

\[
\left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1}: A \rightarrow \left(\forall_ {\mathbf {y} U} ^ {\Psi |} \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right)\left[\left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} \right]. \tag {46}
\]

Now, by the adjunction laws, \(\forall_{\mathbf{y}U}^{\Psi |}\mathrm{reidx}_{\mathbf{y}U}^{\Psi |}\circ \mathrm{unmerid}_{\mathbf{y}U}^{\Psi |} = \mathrm{id},\) so

\[
\forall_ {\mathbf {y} U} ^ {\Psi |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} = \forall_ {\mathbf {y} U} ^ {\Psi |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \circ \operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |} \circ \left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} = \left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1}. \tag {47}
\]

Then we have

\[
\left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1}: A \rightarrow \left(\forall_ {\mathbf {y} U} ^ {\Psi |} \mathfrak {l} _ {\mathbf {y} U} ^ {\Psi |} A\right)\left[ \forall_ {\mathbf {y} U} ^ {\Psi |} \operatorname{reidx} _ {\mathbf {y} U} ^ {\Psi |} \right]. \tag {48}
\]

Thus, we can substitute \(\forall_{\mathbf{y}U}^{\Psi |}B\) with \((\pi ,(\mathrm{unmerid}_{\mathbf{y}U}^{\Psi |})^{-1}(\xi))\), yielding a type in the desired context. We assume that \(\hat{b}\) has this type.

- In the coherence criterion, we have applied operations to \( b_{\partial} \) and \( \hat{b} \) before equating them. We have to ensure that the resulting terms are well-typed in the given context and type.

- If we apply \(\exists_{\mathbf{y}U}^{\Psi|}\) to the term \(\hat{b}\), we get

\[
\Psi \ltimes \mathbf {y} U \mid \left(\exists_ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} \Gamma\right). \exists_ {\mathbf {y} U} ^ {\Psi |} A \vdash^ {\exists_ {\mathbf {y} U} ^ {\Psi |}} \hat {b}: \left(\exists_ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} B\right) \left[ \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\operatorname{unmerid} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right].
\]

If we subsequently apply app \( _{yU}^{\Psi|} \) , we get

\[
\Psi \ltimes \mathbf {y} U \mid \left(\exists_ {\mathbf {y} U} ^ {\Psi |} \forall_ {\mathbf {y} U} ^ {\Psi |} \Gamma\right). \exists_ {\mathbf {y} U} ^ {\Psi |} A \vdash \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \left(\exists_ {\mathbf {y} U} ^ {\Psi |} \hat {b}\right): B \left[ \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \right] \left[ \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\mathsf {u n m e r i d} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right].
\]

Next, we apply \(\Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y}U|}\) and obtain something of type

\[
\left(\Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} B\right) \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \right] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\mathsf {u n m e r i d} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right].
\]

Now if we look at the context of \(\Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y}U|}B\), we see that the last type is the unit type by theorem 4.4.4, so the substitution applied to \(B\) is determined by its weakening. So we rewrite:

\[
\begin{array}{l} \dots = \left(\Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} B\right) [ (\mathrm{id}, \_) ] [ \pi ] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \right] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\mathsf {u n m e r i d} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right] \\ = \left(\Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} B\right) [ (\mathrm{id}, \_) ] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \mathsf {a p p} _ {\mathbf {y} U} ^ {\Psi |} \right] [ \pi ] \left[ \Omega_ {(\in \partial U)} ^ {\Psi \ltimes \mathbf {y} U |} \exists_ {\mathbf {y} U} ^ {\Psi |} \left(\pi , \left(\mathsf {u n m e r i d} _ {\mathbf {y} U} ^ {\Psi |}\right) ^ {- 1} (\xi)\right) \right] \\ \end{array}
\]

37

$$\begin{aligned} & = \left( \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U|} B \right) [(\mathrm{id}, \lrcorner)] \left[ \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U|} \mathsf{app}_{\mathbf{y} U}^{\Psi|} \right] \left[ \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U|} \exists_{\mathbf{y} U}^{\Psi|} \left( \pi \circ \left( \pi, \left( \mathsf{unmerid}_{\mathbf{y} U}^{\Psi|} \right)^{-1} (\xi) \right) \right) \right] \\ & = \left( \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U|} B \right) [(\mathrm{id}, \lrcorner)] \left[ \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U|} \mathsf{app}_{\mathbf{y} U}^{\Psi|} \right] \left[ \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U|} \exists_{\mathbf{y} U}^{\Psi|} \pi \right] \\ & = \left( \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U|} B \right) [(\mathrm{id}, \lrcorner)] \left[ \Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U|} \left( \mathsf{app}_{\mathbf{y} U}^{\Psi|} \circ \pi \right) \right]. \end{aligned}$$

- It is immediate that the substitution applied to $b_{\partial}$ yields the given type.

**Soundness of the coherence criterion.** Note that, if we apply to $b$ the same reasoning that we applied to $B$ to show well-formedness of the last 3 premises, we find that the coherence criterion does hold if $b_{\partial}$ and $\dot{b}$ arise from a common $b$.

**Completeness of the elimination clauses.** We now show that $b$ is fully determined by the $b_{\partial}$ and $\dot{b}$ that can be derived from it. Afterwards, we will show that the given coherence condition is sufficient to make sure that $b_{\partial}$ and $\dot{b}$ determine some $b$.

Note that $B$, being a type in a presheaf CwF, is a presheaf over the category of elements of $\Gamma$. $\left( \begin{array}{c} \S_{\mathbf{y} U}^{\Psi|} A \end{array} \right) \left[ \mathsf{reidx}_{\mathbf{y} U}^{\Psi|} \right]$. Hence it acts on cells

$$\left( V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y} U}, \gamma^{(V, \varphi) \Rightarrow \Gamma}, \alpha^{(V, \varphi, \gamma) \Rightarrow \left( \S_{\mathbf{y} U}^{\Psi|} A \right) \left[ \mathsf{reidx}_{\mathbf{y} U}^{\Psi|} \right]} \right).$$

Now we divide such cells in two classes: on-boundary cells (for which $(V, \varphi)$ is on the boundary) and total cells (the others). As $\Omega_{(\in \partial U)}^{\Psi \ltimes \mathbf{y} U}$ is exactly the restriction of presheaves to the on-boundary cells, it is clear that $b_{\partial}$ determines the action of $b$ on those.

For total cells, note that the full subcategory of $\mathcal{V}/(\Psi \ltimes \mathbf{y} U)$ consisting of the total elements, is (by theorem 4.1.12) equivalent to $\mathcal{W}/\Psi$, with one direction given by $\exists_{U}^{\prime \Psi}$. Restriction to total cells is then given by the central lifting of that functor, being $\forall_{\mathbf{y} U}^{\Psi|}$. Combined with the knowledge that $\forall_{\mathbf{y} U}^{\Psi|} \S_{\mathbf{y} U}^{\Psi|} \cong \mathrm{Id}$ (theorem 4.1.11), this reveals that $\dot{b}$ determines the action of $b$ on total cells.

**Completeness of the coherence criterion.** The action of a term on cells should be natural with respect to restriction. This is automatic when considered with respect to morphisms between cells that are either both total or both on-boundary. Moreover, there are no morphisms $\chi: (V, \varphi) \to (V', \varphi'): \mathcal{V}/(\Psi \ltimes U)$ from a total cell to an on-boundary cell, since the boundary is a well-defined presheaf. So we still need to prove naturality w.r.t. morphisms from on-boundary cells to total cells.

Let $\chi: (V, \varphi) \to (V', \varphi')$ be such a morphism. Then $(V', \varphi') \cong_{\iota} \exists_{U}^{\prime \Psi}(W, \psi) \cong \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi}(W, \psi) \cong \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi}(V', \varphi')$ by an isomorphism

$$\begin{aligned} & \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi} \iota^{-1} \circ \exists_{U}^{\prime \Psi} (\mathsf{drop}_{U}^{\prime \Psi})^{-1} \circ \iota \\ & = \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi} \iota^{-1} \circ \mathsf{copy}_{U}^{\prime \Psi} \circ \iota \\ & = \mathsf{copy}_{U}^{\prime \Psi} \circ \iota^{-1} \circ \iota = \mathsf{copy}_{U}^{\prime \Psi}. \end{aligned}$$

Hence, by naturality, $\chi = (\mathsf{copy}_{U}^{\prime \Psi})^{-1} \circ \mathsf{copy}_{U}^{\prime \Psi} \circ \chi = (\mathsf{copy}_{U}^{\prime \Psi})^{-1} \circ \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi} \chi \circ \mathsf{copy}_{U}^{\prime \Psi}$. Thus, we have factored $\chi$ as an instance of the unit $\mathsf{copy}_{U}^{\prime \Psi}$ followed by a morphism between total cells. This means it is sufficient to show naturality with respect to $\mathsf{copy}_{U}^{\prime \Psi}: (V, \varphi) \to \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi}(V, \varphi)$. (The cells of $\Gamma$ and the transpension type available for $(V', \varphi')$ carry over to $\exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi}(V, \varphi)$ by restriction.)

Now the action of $b$ on $(V, \varphi)$ is given by the action of $b_{\partial}$ on $(V, \varphi)$. Meanwhile, the action of $b$ on $\exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi}(V, \varphi)$ is given by the action of $\dot{b}$ on $\exists_{U}^{\prime \Psi}(V, \varphi)$, which is the action of $\exists_{U}^{\prime \Psi} \dot{b}$ on $(V, \varphi)$. These have to correspond via $\mathsf{copy}_{U}^{\prime \Psi}: (V, \varphi) \to \exists_{U}^{\prime \Psi} \exists_{U}^{\prime \Psi}(V, \varphi)$, which corresponds via central lifting to the natural transformation $\mathsf{app}_{\mathbf{y} U}^{\Psi|}$ on presheaves. This is exactly what happens in the coherence criterion: we use $\mathsf{app}_{\mathbf{y} U}^{\Psi|}: \exists_{\mathbf{y} U}^{\Psi|} \forall_{\mathbf{y} U}^{\Psi|} \to \mathrm{Id}$ to bring $b_{\partial}$ and $\dot{b}$ to the same context and type, and then equate them. Since $b_{\partial}$ only exists on the boundary, we also have to restrict $\dot{b}$ to the boundary, but that's OK since we were interested in an on-boundary cell anyway.

38

Example 4.4.8 (Affine cubes). We instantiate theorem 4.4.7 for the multiplier \(\sqcup * \mathbb{I} : \square^k \to \square^k\) (example 3.3.3). There, \(\partial \mathbb{I}\) is essentially the constant presheaf with \(k\) elements. So \(b_{\partial}\) determines the images of the \(k\) poles of the transpension type. The term \(b\) determines the action on paths (for \(k = 2\), for general \(k\) perhaps 'webs' is a better term), and the paths/webs of the transpension type are essentially the elements of \(A\). The coherence condition says that the image of such paths/webs should always have the endpoints given by \(b_{\partial}\).

Example 4.4.9 (Clocks). We instantiate theorem 4.4.7 for the multiplier \(\sqcup * (i : \odot_k)\) (example 3.3.6), where we adapt the base category to forbid diagonals: a morphism may use every variable of its domain at most once. The boundary \(\partial(i : \odot_k)\) is isomorphic to \(\mathbf{y}(i : \odot_{k-1})\) if \(k > 0\) and to the empty presheaf \(\bot\) if \(k = 0\). So if we want to eliminate an element of the transpension type over \(\mathbf{y}(i : \odot_k)\), which means we have a clock and we don't care about what happens if the time exceeds \(k\), then we need to handle two cases. The first case \(b_{\partial}\) says what happens if we don't even care what happens at timestamp \(k\); in which case the transpension type trivializes. Then, by giving \(b\), we say what happens at timestamp \(k\) and need to make sure that this is consistent with \(b_{\partial}\). The elements of the transpension type at timestamp \(k\) are essentially the elements of \(A\), which are fresh for the clock.

Example 4.4.10 (Embargoes). Recall that the multiplier \(\sqcup \ltimes \mathbf{!}\) sends \(W \in \mathcal{W}\) to \((W, \top) \in \mathcal{W} \times \uparrow\), the Yoneda-embedding of which represents the arrow \(\mathbf{y}W \to \mathbf{y}W\), i.e. \(\mathbf{y}W \mathbf{!}, \top\) under the convention that \(\Psi \mathbf{!}, \Theta\) denotes \((\Psi, \Theta \to \Psi)\). Its left lifting is \(\sqcup \ltimes \mathbf{y} \mathbf{!}: \widehat{\mathcal{W}} \to \widehat{\mathcal{W} \times \uparrow}\), and \(\mathbf{y} \mathbf{!}\) is the terminal object, so that \(\widehat{\mathcal{W} \times \uparrow} / \mathbf{y} \mathbf{!} \cong \widehat{\mathcal{W} \times \uparrow}\). We get 5 adjoint functors, of which we give here the action up to isomorphism:

\[
\begin{array}{c c c c c c c} & & & \Psi & \mapsto & (\bot \to \Psi), \\ & & \exists_ {\mathbf {y} \mathbf {!}} & : & \Psi & \leftrightarrow & (\Psi . \Theta \to \Psi), \\ \sqcup \ltimes \mathbf {y} \mathbf {!} & \text {or} & \exists_ {\mathbf {y} \mathbf {!}} & : & \Psi & \mapsto & (\Psi \to \Psi), \\ \mathbf {y} \mathbf {!} \multimap \sqcup & \text {or} & \forall_ {\mathbf {y} \mathbf {!}} & : & \Psi . \Theta & \leftrightarrow & (\Psi . \Theta \to \Psi), \\ \mathbf {y} \mathbf {!} \vee \sqcup & \text {or} & \Diamond_ {\mathbf {y} \mathbf {!}} & : & \Psi & \mapsto & (\Psi \to \top). \end{array}
\]

The boundary of  \( y! \)  is  \( \partial! \cong y(\top, \bot) \)  which is isomorphic to the arrow  \( \bot \to \top \) . Thus, we see:

\( \exists_{y!} \)  If, for some unknown embargo, we have information partly under that embargo, then we can only extract the unembargoed information,

\( \perp_{y!} \)  If information is fresh for an embargo, then it is unembargoed,

\( \forall_{y!} \)  If, for any embargo, we have information partly under that embargo, then we can extract the information,

\( \Diamond_{y!} \)  If information is transpended over an embargo, then it is completely embargoed.

Perhaps the above is more intuitive if we think of an embargo as a key or a password.

So let us now instantiate theorem 4.4.7, which allows us to eliminate an element of the transpension type, i.e. essentially an element of \( A \to \top \). The boundary case exists over the boundary \( \bot \to \top \) and allows us to consider only the codomain of the arrow, i.e. the part of the context before the embargo, where the transpension type is trivial. The case \( b \) then requires us to say how to act on embargoed data in a coherent way with what we already specified in \( b_{\partial} \). The embargoed data is essentially an element of \( A \), which comes from the mode where the embargo does not apply.

## 5 Prior modalities

Many modalities arise as central or right liftings of functors between base categories [NVD17, ND18, Nuy18, BM20]. The following definition allows us to use such modalities even when part of the context is in front of a pipe.

Definition 5.0.1. A functor \( G: \mathcal{W} \to \mathcal{W}' \) yields a functor \( G'^{\Psi}: \mathcal{W}/\Psi \to \mathcal{W}'/G_{!}\Psi : (W, \psi) \mapsto (GW, G_{!}\psi) \). This in turn yields three adjoint functors between presheaf categories:

\[
G _ {!} ^ {\Psi !} \dashv G ^ {\Psi ! *} \dashv G _ {*} ^ {\Psi !}. \tag {49}
\]

39

If a modality is both a right and a central lifting, then the following theorem relates the corresponding 'piped' modalities:

Theorem 5.0.2. If \( G: \mathcal{W} \to \mathcal{W}' \) has a right adjoint \( G \dashv S \), then we have

\[
\begin{array}{c c c c c c c c c c} & & \Sigma^ {\prime \varepsilon_ {!}} \circ G ^ {\prime S _ {!} \Psi^ {\prime}} & \dashv & S ^ {\prime \Psi^ {\prime}} & G ^ {\prime \Psi} & \dashv & \Omega^ {\prime \eta_ {!}} \circ S ^ {\prime G _ {!} \Psi} \\ \hline & & \Sigma^ {\varepsilon_ {!}} \circ G _ {!} ^ {S _ {!} \Psi^ {\prime}} & \dashv & S _ {!} ^ {\Psi^ {\prime}} & G _ {!} ^ {\Psi |} & \dashv & \Omega^ {\eta_ {!}} \circ S _ {!} ^ {G _ {!} \Psi |} & \cong & G ^ {\Psi | *} \\ S _ {!} ^ {\Psi^ {\prime}} | & \cong & G ^ {S _ {!} \Psi^ {\prime} | *} \circ \Omega^ {\varepsilon_ {!}} | & \dashv & S ^ {\Psi^ {\prime} | *} & G ^ {\Psi | *} & \dashv & S ^ {G _ {!} \Psi | *} \circ \Pi^ {\eta_ {!}} | & \cong & G _ {*} ^ {\Psi |} \\ S ^ {\Psi^ {\prime} | *} & \cong & \Pi^ {\varepsilon_ {!}} \circ G _ {*} ^ {S _ {!} \Psi^ {\prime}} | & \dashv & S _ {*} ^ {\Psi^ {\prime}} | & G _ {*} ^ {\Psi |} & \dashv & \S^ {\eta_ {!}} \circ S _ {*} ^ {G _ {!} \Psi |} \end{array} \tag {50}
\]

assuming - where mentioned - that \(\Omega^{\prime \eta_{!}}\) exists.

Proof. For the left half of the table, we only prove the first line. The other adjunctions follow from the fact that \(\sqcup_{!},\sqcup^{*}\) and \(\sqcup_{*}\) are pseudofunctors, and the isomorphisms follow from uniqueness of the adjoint. We have a correspondence of diagrams

![img-16.jpeg](img-16.jpeg)

![img-17.jpeg](img-17.jpeg)

i.e. morphisms \((W,\psi)\to S^{\prime /\Psi^{\prime}}(W^{\prime},\psi^{\prime}):\mathcal{W} / S_{!}\Psi^{\prime}\) correspond to morphisms \(\Sigma^{\prime \varepsilon_1}G^{\prime S_1\Psi^{\prime}}(W,\psi)\to\) \((W^{\prime},\psi^{\prime}):\mathcal{W}^{\prime} / \Psi^{\prime}\).

On the right side of the table, we similarly only need to prove the first line, and we prove it from the first line on the left side. The left adjoint to \(\Omega^{\prime \eta_{!}}\circ S^{\prime G_{!}\Psi}\) is \(\left(\Sigma^{\prime \varepsilon_{!}}\circ G^{\prime S_{!}G_{!}\Psi}\right)\circ \Sigma^{\prime \eta_{!}}\). We prove that this is equal to \(G^{\prime \Psi}\):

\[
\begin{array}{l} \Sigma^ {\prime \varepsilon_ {!}} G ^ {\prime S _ {!} G _ {!} \Psi} \Sigma^ {\prime \eta_ {!}} (W, \psi : W \to \Psi) \\ = \Sigma^ {\prime \varepsilon_ {!}} G ^ {\prime S _ {!} G _ {!} \Psi} (W, \eta_ {!} \circ \psi : W \rightarrow S _ {!} G _ {!} \Psi) \\ = \Sigma^ {\prime \varepsilon_ {!}} (G W, G _ {!} \eta_ {!} \circ G _ {!} \psi : G W \rightarrow G _ {!} S _ {!} G _ {!} \Psi) \\ = (G W, \varepsilon_ {!} \circ G _ {!} \eta_ {!} \circ G _ {!} \psi : G W \rightarrow G _ {!} \Psi) = (G W, G _ {!} \psi : G W \rightarrow G _ {!} \Psi). \\ \end{array}
\]

## 6 Commutation rules

### 6.1 Substitution and substitution

See theorem 2.3.18.

### 6.2 Modality and substitution

Theorem 6.2.1. Assume a functor \( G: \mathcal{W} \to \mathcal{W}' \) and a morphism \( \sigma: \Psi_1 \to \Psi_2: \widehat{\mathcal{W}} \). Then we have a commutative diagram

\[
\begin{array}{c} \mathcal {W} / \Psi_ {1} \xrightarrow {G ^ {\prime} \Psi_ {1}} \mathcal {W} ^ {\prime} / G _ {!} \Psi_ {1} \\ \Sigma^ {\prime \sigma} \Bigg \downarrow \quad \Bigg \downarrow \Sigma^ {\prime G _ {!} \sigma} \\ \mathcal {W} / \Psi_ {2} \xrightarrow [ G ^ {\prime} \Psi_ {2} ]{} \mathcal {W} ^ {\prime} / G _ {!} \Psi_ {2} \end{array} \tag {52}
\]

and hence

|   | \( G_{!} \) | \( G^{*} \) | \( G_{*} \)  |
| --- | --- | --- | --- |
|  \( \Sigma \) | \( \Sigma^{G_{!}\sigma|}G_{!}^{\Psi_{1}|} \cong G_{!}^{\Psi_{2}|}\Sigma^{\sigma|} \) | \( \Sigma^{\sigma|}G^{\Psi_{1}|*} \to G^{\Psi_{2}|*}\Sigma^{G_{!}\sigma|} \) |   |
|  \( \Omega \) | \( \Omega^{G_{!}\sigma|}G_{!}^{\Psi_{2}|} \leftarrow G_{!}^{\Psi_{1}|}\Omega^{\sigma|} \) | \( \Omega^{\sigma|}G^{\Psi_{2}|*} = G^{\Psi_{1}|*}\Omega^{G_{!}\sigma|} \) | \( \Omega^{G_{!}\sigma|}G_{*}^{\Psi_{2}|} \to G_{*}^{\Psi_{1}|}\Omega^{\sigma|} \)  |
|  \( \Pi \) |  | \( \Pi^{\sigma|}G^{\Psi_{1}|*} \leftarrow G^{\Psi_{2}|*}\Pi^{G_{!}\sigma|} \) | \( \Pi^{G_{!}\sigma|}G_{*}^{\Psi_{1}|} \cong G_{*}^{\Psi_{2}|}\Pi^{\sigma|} \)  |
|  \( \S \) |  |  | \( \S^{G_{!}\sigma|}G_{*}^{\Psi_{2}|} \leftarrow G_{*}^{\Psi_{1}|}\S^{\sigma|} \)  |

40

where every statement holds if the mentioned functors exist.

Proof. It is evident from the definitions that the given diagram commutes. Then by applying \(\sqcup^{*}\), we find the that \(\Omega^{\sigma}|G^{\Psi_2|*} = G^{\Psi_1|*}\Omega^{G_1\sigma|}\). The rest of the table then follows by lemma 2.1.2.

Remark 6.2.2. • If \(\sigma = \pi : \Psi.A \to \Psi\), then this says something about weakening and the \(\Sigma\)- and \(\Pi\)-types over \(A\).

- If \( G_{!} \) moreover happens to be a CwF morphism, then this relates weakening and the \( \Sigma \)- and \( \Pi \)-types over \( A \) to those over \( G_{!}A \).
- If \(\sqcup \times U\) is a cartesian multiplier and we take \(\sigma = \pi_1: \Psi \times \mathbf{y}U \to \Psi\), then by theorem 4.1.11, this says something about \(\exists_{\mathbf{y}U}^{\Psi|} \dashv \exists_{\mathbf{y}U}^{\Psi|} \dashv \forall_{\mathbf{y}U}^{\Psi|} \dashv \emptyset_{\mathbf{y}U}^{\Psi|}\).

### 6.3 Multiplier and substitution

If, in section 6.2, we take \(G\) equal to some multiplier \(\sqcup \ltimes U:\mathcal{W}\to \mathcal{V}\), then we have

\[
G ^ {/ \Psi} = \exists_ {U} ^ {/ \Psi}, \quad G _ {!} = \sqcup \ltimes \mathbf {y} U, \quad G _ {!} ^ {\Psi |} = \exists_ {\mathbf {y} U} ^ {\Psi |}, \quad G ^ {\Psi | *} = \forall_ {\mathbf {y} U} ^ {\Psi |}, \quad G _ {*} ^ {\Psi |} = \emptyset_ {\mathbf {y} U} ^ {\Psi |}. \tag {53}
\]

This immediately yields the general case of the following theorem:

Theorem 6.3.1. Assume a multiplier \(\sqcup \ltimes U:\mathcal{W}\to \mathcal{V}\) and a morphism \(\sigma :\Psi_1\to \Psi_2\) in \(\widehat{\mathcal{W}}\). Write \(\tau = \sigma \ltimes \mathbf{y}U\). Then we have:

|   | \( \exists \) | \( \bot \) | \( \forall \) | \( \emptyset \)  |
| --- | --- | --- | --- | --- |
|  \( \Sigma \) | \( \Sigma^{\sigma}|\exists_{\mathbf{y}U}^{\Psi_1}| \triangleleft^{1} \exists_{\mathbf{y}U}^{\Psi_2}|\Sigma^{\tau}| \) | \( \Sigma^{\tau}|\exists_{\mathbf{y}U}^{\Psi_1}| \cong \exists_{\mathbf{y}U}^{\Psi_2}|\Sigma^{\sigma}| \) | \( \Sigma^{\sigma}|\forall_{\mathbf{y}U}^{\Psi_1}| \triangleright_{1} \forall_{\mathbf{y}U}^{\Psi_2}|\Sigma^{\tau}| \) | \( \Sigma^{\tau}|\emptyset_{\mathbf{y}U}^{\Psi_1}| \triangleright_{2} \emptyset_{\mathbf{y}U}^{\Psi_2}|\Sigma^{\sigma}| \)  |
|  \( \Omega \) | \( \Omega^{\sigma}|\exists_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{2} \exists_{\mathbf{y}U}^{\Psi_1}|\Omega^{\tau}| \) | \( \Omega^{\tau}|\exists_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{1} \exists_{\mathbf{y}U}^{\Psi_1}|\Omega^{\sigma}| \) | \( \Omega^{\sigma}|\forall_{\mathbf{y}U}^{\Psi_2}| = \forall_{\mathbf{y}U}^{\Psi_1}|\Omega^{\tau}| \) | \( \Omega^{\tau}|\emptyset_{\mathbf{y}U}^{\Psi_2}| \triangleright_{1} \emptyset_{\mathbf{y}U}^{\Psi_1}|\Omega^{\sigma}| \)  |
|  \( \Pi \) | \( \Pi^{\sigma}|\exists_{\mathbf{y}U}^{\Psi_1}| \triangleleft^{3} \exists_{\mathbf{y}U}^{\Psi_2}|\Pi^{\tau}| \) | \( \Pi^{\tau}|\exists_{\mathbf{y}U}^{\Psi_1}| \triangleleft^{2} \exists_{\mathbf{y}U}^{\Psi_2}|\Pi^{\sigma}| \) | \( \Pi^{\sigma}|\forall_{\mathbf{y}U}^{\Psi_1}| \triangleleft^{1} \forall_{\mathbf{y}U}^{\Psi_2}|\Pi^{\tau}| \) | \( \Pi^{\tau}|\emptyset_{\mathbf{y}U}^{\Psi_1}| \cong \emptyset_{\mathbf{y}U}^{\Psi_2}|\Pi^{\sigma}| \)  |
|  \( \$ \) |  | \( \$\tau|\exists_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{3} \exists_{\mathbf{y}U}^{\Psi_1}|\$\sigma| \) | \( \$\sigma|\forall_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{2} \forall_{\mathbf{y}U}^{\Psi_1}|\$\tau| \) | \( \$\tau|\emptyset_{\mathbf{y}U}^{\Psi_2}| \triangleleft^{1} \emptyset_{\mathbf{y}U}^{\Psi_1}|\$\sigma| \)  |

where every statement holds if the mentioned functors exist, and where

1. In general, \(\triangleleft^1\) means \(\leftarrow\), \(\triangleright_1\) means \(\rightarrow\) and the other symbols mean nothing.
2. If \(\sqcup \ltimes U\) is \(\top\)-slice right adjoint, then \(\triangleleft^1\) upgrades to \(\cong\) and \(\triangleleft^2\) upgrades to \(\leftarrow\).
3. If \(\sqcup \ltimes U\) is cartesian (hence \(\top\)-slice right adjoint), then \(\triangleleft^1\) and \(\triangleleft^2\) upgade to \(\cong\) and \(\triangleleft^3\) upgrades to \(\leftarrow\).
4. If \(\sqcup \ltimes U\) is \(\top\)-slice fully faithful, then we have

\[
\Sigma^ {\sigma |} \forall_ {\mathbf {y} U} ^ {\Psi_ {1} |} \cong \forall_ {\mathbf {y} U} ^ {\Psi_ {2} |} \Sigma^ {\tau |}: \overbrace {\mathcal {V} / (\Psi_ {1} \ltimes \mathbf {y} U)} ^ {\text {   }} \to \widehat {\mathcal {W} / \Psi_ {2}} \tag {55}
\]

so that \(\triangleright_{1}\) upgrades to \(\cong\) and \(\triangleright_{2}\) upgrades to \(\rightarrow\).

Proof. 1. The general case is a corollary of theorem 6.2.1 for \( G = \sqcup \ltimes U \).

2. To prove the \(\top\)-slice right adjoint case, we show in the base category that \(\Sigma^{\prime\sigma}\exists_{U}^{\prime\Psi_{1}} = \exists_{U}^{\prime\Psi_{2}}\Sigma^{\prime(\sigma\times\mathbf{y}U)}\). We use the construction of \(\exists_{U}^{\prime\Psi}\) in the proof of presheafwise right adjointness (proposition 4.1.9). On one hand, we have:

\[
\Sigma^ {\prime \sigma} \exists_ {U} ^ {\prime \Psi_ {1}} (V, (\psi_ {1} ^ {W _ {0} \Rightarrow \Psi_ {1}} \ltimes \mathbf {y} U) \circ \varphi^ {V \Rightarrow W _ {0} \ltimes U}) = \Sigma^ {\prime \sigma} \Sigma^ {\prime \psi_ {1}} \exists_ {U} ^ {\prime W _ {0}} (V, \varphi) = \Sigma^ {\prime \sigma \circ \psi_ {1}} \exists_ {U} ^ {\prime W _ {0}} (V, \varphi).
\]

On the other hand:

\[
\begin{array}{l} \exists_ {U} ^ {\prime \Psi_ {2}} \Sigma^ {\prime (\sigma \ltimes \mathbf {y} U)} (V, (\psi_ {1} ^ {W _ {0} \Rightarrow \Psi_ {1}} \ltimes \mathbf {y} U) \circ \varphi^ {V \Rightarrow W _ {0} \ltimes U}) = \exists_ {U} ^ {\prime \Psi_ {2}} (V, ((\sigma \circ \psi_ {1}) \ltimes \mathbf {y} U) \circ \varphi) \\ = \Sigma^ {\prime \sigma \circ \psi_ {1}} \exists_ {U} ^ {\prime W _ {0}} (V, \varphi). \\ \end{array}
\]

41

3. This follows from theorem 2.3.18.

4. We show that \(\Sigma^{\sigma}|\forall_{\mathbf{y}U}^{\Psi_1|}\cong \forall_{\mathbf{y}U}^{\Psi_2|}\Sigma^{\tau |}\). Pick a presheaf \(\Gamma\) over \(\mathcal{V} / (\Psi_1\times \mathbf{y}U)\). On the one hand, we have:

\[
\begin{array}{l} (W _ {2}, \psi_ {2} ^ {W _ {2} \Rightarrow \Psi_ {2}}) \Rightarrow \Sigma^ {\sigma |} \forall_ {\mathbf {y} U} ^ {\Psi_ {1} |} \Gamma \\ = \exists (W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}). (\theta : (W _ {2}, \psi_ {2}) \rightarrow \Sigma^ {\prime \sigma} (W _ {1}, \psi_ {1})) \times ((W _ {1}, \psi_ {1}) \Rightarrow \forall_ {\mathbf {y} U} ^ {\Psi_ {1}} | \Gamma) \\ = \exists (W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}). (\theta : (W _ {2}, \psi_ {2}) \rightarrow (W _ {1}, \sigma \circ \psi_ {1})) \times ((W _ {1} \ltimes U, \psi_ {1} \ltimes \mathbf {y} U) \Rightarrow \Gamma) \\ \cong \exists W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}, \theta^ {W _ {2} \rightarrow W _ {1}}. (\psi_ {2} = \sigma \circ \psi_ {1} \circ \theta) \times ((W _ {1} \ltimes U, \psi_ {1} \ltimes \mathbf {y} U) \Rightarrow \Gamma) \\ \end{array}
\]

We now absorb \(\theta\) into \(\psi_{1}\):

\[
\cong \psi_ {1} ^ {W _ {2} \Rightarrow \Psi_ {1}}. (\psi_ {2} = \sigma \circ \psi_ {1}) \times ((W _ {2} \ltimes U, \psi_ {1} \ltimes \mathbf {y} U) \Rightarrow \Gamma).
\]

On the other hand, we have:

\[
\begin{array}{l} (W _ {2}, \psi_ {2} ^ {W _ {2} \Rightarrow \Psi_ {2}}) \Rightarrow \forall_ {\mathbf {y} U} ^ {\Psi_ {2} |} \Sigma^ {\tau |} \Gamma \\ = \left(W _ {2} \ltimes U, \psi_ {2} \ltimes \mathbf {y} U\right) \Rightarrow \Sigma^ {\tau |} \Gamma \\ = \exists (V _ {1}, \varphi_ {1} ^ {V _ {1} \Rightarrow \Psi_ {1} \ltimes \mathbf {y} U}). (\omega : (W _ {2} \ltimes U, \psi_ {2} \ltimes \mathbf {y} U) \rightarrow \Sigma^ {\prime \tau} (V _ {1}, \varphi_ {1})) \times ((V _ {1}, \varphi_ {1}) \Rightarrow \Gamma) \\ = \exists (V _ {1}, \varphi_ {1} ^ {V _ {1} \Rightarrow \Psi_ {1} \ltimes \mathbf {y} U}). (\omega : (W _ {2} \ltimes U, \psi_ {2} \ltimes \mathbf {y} U) \rightarrow (V _ {1}, (\sigma \ltimes \mathbf {y} U) \circ \varphi_ {1})) \times ((V _ {1}, \varphi_ {1}) \Rightarrow \Gamma) \\ \end{array}
\]

We now deconstruct \(\varphi_{1} = (\psi_{1}\ltimes \mathbf{y}U)\circ \chi\)

\[
\begin{array}{l} \cong \exists V _ {1}, W _ {1}, \chi^ {V _ {1} \rightarrow W _ {1} \ltimes U}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}. \\ (\omega : (W _ {2} \ltimes U, \psi_ {2} \ltimes \mathbf {y} U) \rightarrow (V _ {1}, ((\sigma \circ \psi_ {1}) \ltimes \mathbf {y} U) \circ \chi)) \times ((V _ {1}, (\psi_ {1} \ltimes \mathbf {y} U) \circ \chi) \Rightarrow \Gamma) \\ \cong \exists V _ {1}, W _ {1}, \chi^ {V _ {1} \rightarrow W _ {1} \ltimes U}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}, \omega^ {W _ {2} \ltimes U \rightarrow V _ {1}}. \\ (\psi_ {2} \ltimes \mathbf {y} U = ((\sigma \circ \psi_ {1}) \ltimes \mathbf {y} U) \circ \chi \circ \omega) \times ((V _ {1}, (\psi_ {1} \ltimes \mathbf {y} U) \circ \chi) \Rightarrow \Gamma) \\ \end{array}
\]

We now absorb \(\omega\) into \(\chi\):

\[
\begin{array}{l} \cong \exists W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}, \chi^ {W _ {2} \ltimes U \rightarrow W _ {1} \ltimes U}. \\ \left(\psi_ {2} \ltimes \mathbf {y} U = \left(\left(\sigma \circ \psi_ {1}\right) \ltimes \mathbf {y} U\right) \circ \chi\right) \times \left(\left(W _ {2} \ltimes U, \left(\psi_ {1} \ltimes \mathbf {y} U\right) \circ \chi\right) \Rightarrow \Gamma\right) \\ \text {   Let   } \chi = \mathbb {J} _ {U} ^ {\prime \Psi_ {2}} \theta : \mathbb {J} _ {U} ^ {\prime \Psi_ {2}} (W _ {2}, \psi_ {2}) \to \mathbb {J} _ {U} ^ {\prime \Psi_ {2}} (W _ {1}, \sigma \circ \psi_ {1}): \\ \cong \exists W _ {1}, \psi_ {1} ^ {W _ {1} \Rightarrow \Psi_ {1}}, \theta^ {W _ {2} \rightarrow W _ {1}}. (\psi_ {2} = \sigma \circ \psi_ {1} \circ \theta) \times ((W _ {2} \ltimes U, ((\psi_ {1} \circ \theta) \ltimes \mathbf {y} U)) \Rightarrow \Gamma) \\ \end{array}
\]

We now absorb \(\theta\) into \(\psi_{1}\):

\[
\cong \psi_ {1} ^ {W _ {2} \Rightarrow \Psi_ {1}}. (\psi_ {2} = \sigma \circ \psi_ {1}) \times ((W _ {2} \ltimes U, (\psi_ {1} \ltimes \mathbf {y} U)) \Rightarrow \Gamma)
\]

This proves the isomorphism. The rest follows from lemma 2.1.2.

### 6.4 Multiplier and modality

Theorem 6.4.1. Assume a commutative diagram (up to natural isomorphism \(\nu : F(\sqcup \ltimes U) \cong G_{\sqcup} \ltimes U'\))

\[
\begin{array}{c} \mathcal {W} \xrightarrow {G} \mathcal {W} ^ {\prime} \\ \sqcup \ltimes U \Bigg | _ {\downarrow} \quad \Bigg | _ {\downarrow} \sqcup \ltimes U ^ {\prime} \\ \mathcal {V} \xrightarrow [ F ]{} \mathcal {V} ^ {\prime} \end{array} \tag {56}
\]

where \(\sqcup \ltimes U\) and \(\sqcup \ltimes U'\) are multipliers for \(U\) and \(U'\).

Then \(\Sigma^{\prime / \nu}\) is a strictly invertible functor and hence we have

\[
\Sigma^ {\nu_ {i} |} \cong \Omega^ {\nu_ {i} ^ {- 1} |} \cong \Pi^ {\nu_ {i} |} \cong \delta^ {\nu_ {i} ^ {- 1} |} \quad \Sigma^ {\nu_ {i} ^ {- 1} |} \cong \Omega^ {\nu_ {i} |} \cong \Pi^ {\nu_ {i} ^ {- 1} |} \cong \delta^ {\nu_ {i} |}, \tag {57}
\]

42

where \(\Omega^{\nu_1^{-1}}\) is the strict inverse to \(\Omega^{\nu_1}\).

Then we have \(\Sigma^{\prime \nu_1^{-1}}\mathbb{J}_{U'}^{\prime G_1\Psi}G / \Psi \cong F / \Psi \ltimes U\mathbb{J}_U^{\prime \Psi}\). This yields the following commutation table:

|   | \( F_{!},G_{!} \) | \( F^{*},G^{*} \) | \( F_{*},G_{*} \)  |
| --- | --- | --- | --- |
|  \( \exists \) | \( \exists_{\mathbf{y}U}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}|F_{!}^{\Psi\ltimes\mathbf{y}U}| \triangleright_{1}G_{!}^{\Psi}\exists_{\mathbf{y}U}^{\Psi}| \) | \( \exists_{\mathbf{y}U}^{\Psi}|F^{\Psi*}\triangleright_{2}G^{\Psi*}\exists_{\mathbf{y}U'}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}| \) |   |
|  \( \bot \) | \( \Omega^{\nu_{1}}|\exists_{\mathbf{y}U'}^{G_{!}\Psi}G_{!}^{\Psi}\cong F_{!}^{\Psi\ltimes\mathbf{y}U}| \exists_{\mathbf{y}U}^{\Psi}| \) | \( \exists_{\mathbf{y}U}^{\Psi}|G^{\Psi*}\triangleright_{1}F^{\Psi\ltimes\mathbf{y}U*}\Omega^{\nu_{1}}|\exists_{\mathbf{y}U'}^{G_{!}\Psi}| \) | \( \Omega^{\nu_{1}}|\exists_{\mathbf{y}U'}^{G_{!}\Psi}G_{*}^{\Psi}\triangleright_{2}F_{*}^{\Psi\ltimes\mathbf{y}U}| \exists_{\mathbf{y}U}^{\Psi}| \)  |
|  \( \forall \) | \( \forall_{\mathbf{y}U'}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}|F_{!}^{\Psi\ltimes\mathbf{y}U}| \leftarrow G_{!}^{\Psi}\forall_{\mathbf{y}U}^{\Psi}| \) | \( \forall_{\mathbf{y}U}^{\Psi}|F^{\Psi*}\cong G^{\Psi*}\forall_{\mathbf{y}U'}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}| \) | \( \forall_{\mathbf{y}U'}^{G_{!}\Psi}\Omega^{\nu_{1}^{-1}}|F_{*}^{\Psi\ltimes\mathbf{y}U}| \triangleright_{1}G_{*}^{\Psi}\forall_{\mathbf{y}U}^{\Psi}| \)  |
|  \( \Diamond \) |  | \( \Diamond_{\mathbf{y}U}^{\Psi}|G^{\Psi*}\leftarrow F^{\Psi\ltimes\mathbf{y}U*}\Omega^{\nu_{1}}|\Diamond_{\mathbf{y}U'}^{G_{!}\Psi}| \) | \( \Omega^{\nu_{1}}|\Diamond_{\mathbf{y}U'}^{G_{!}\Psi}G_{*}^{\Psi}\cong F_{*}^{\Psi\ltimes\mathbf{y}U}| \Diamond_{\mathbf{y}U}^{\Psi}| \)  |

where any statement holds if the mentioned functors exist, and where

1. In general, \(\triangleright_{1}\) means \(\rightarrow\) and \(\triangleright_{2}\) means nothing.
2. If \(\mathcal{W} = \mathcal{V}\), \(\mathcal{W}' = \mathcal{V}'\), \(F = G\), both multipliers are cartesian and \(\nu\) respects the first projection, i.e. \(\pi_1 \circ \nu = G\pi_1\), then \(\triangleright_1\) upgrades to \(\cong\) and \(\triangleright_2\) upgrades to \(\rightarrow\). Note that in this case we have \(GU \cong G(\top \times U) \cong_{\nu} G\top \times U'\).

Remark 6.4.2. In the above theorem, we think of \( F \) and \( G \) as similar functors; if we are dealing with endomultipliers, we will typically take \( F = G \). The multipliers, however, will typically be different, as in general \( U \not\cong FU \).

Proof. Since \(\nu_{!}\) is an isomorphism, \(\Sigma^{\prime \nu_{!}}\) is a strictly invertible functor with inverse \(\Sigma^{\prime \nu_{1}^{-1}}\). Since \(\sqcup^{*}\) is a 2-functor, \(\Omega^{\nu_{1}}\) is also strictly invertible with inverse \(\Omega^{\nu_{1}^{-1}}\). Because equivalences of categories are adjoint to their inverse, we get the chains of isomorphisms displayed.

1. The given commutation property in the base category follows immediately from the definitions and naturality of \(\nu\) and its image under \(\sqcup_{!}\). The rest of the table then follows by lemma 2.1.2.
2. We invoke theorem 6.2.1 with \(\sigma = \pi_2: \Psi \times \mathbf{y}U \to \Psi\). This yields \(\Omega_{\mathbf{y}U}^{\Psi}|G^{\Psi*} = G^{\Psi \times \mathbf{y}U*}\Omega^{G_1\pi_2|}\). Now \(G_1\pi_2 = \pi_2 \circ \nu_1\) so we can rewrite this to \(\Omega_{\mathbf{y}U}^{\Psi}|G^{\Psi*} = G^{\Psi \times \mathbf{y}U*}\Omega^{\nu_1|}\Omega_{\mathbf{y}U'}^{G_1\Psi|}\). The rest of the table then follows by lemma 2.1.2.

### 6.5 Multiplier and multiplier

Theorem 6.5.1. Assume we have a commutative diagram (up to natural isomorphism \(\nu : \sqcup \ltimes U \ltimes I \cong \sqcup \ltimes J \ltimes U'\)) of multipliers

\[
\begin{array}{c} \mathcal {W} \xrightarrow {\sqcup \ltimes J} \mathcal {W} ^ {\prime} \\ \sqcup \ltimes U \Bigg | _ {\downarrow} \quad \Bigg | _ {\sqcup \ltimes U ^ {\prime}} \\ \mathcal {V} \xrightarrow {\sqcup \ltimes I} \mathcal {V} ^ {\prime}. \end{array} \tag {58}
\]

Then we have the commutation table given in fig. 1 where every statement holds if the mentioned functors exist, and where

1. In general, \(\triangleright_{1}\) means \(\rightarrow\), \(\triangleleft^{1}\) means \(\leftarrow\) and the other symbols mean nothing.
2. If \(\mathcal{W} = \mathcal{W}'\), \(\mathcal{V} = \mathcal{V}'\), \(\sqcup \ltimes U = \sqcup \ltimes U'\), the multipliers \(\sqcup \ltimes J\) and \(\sqcup \ltimes I\) are cartesian and \((\pi_1 \ltimes U) \circ \nu = \pi_1 : (\sqcup \ltimes U) \times I \to \sqcup \ltimes U\), then \(\triangleleft^1\) upgrades to \(\cong\) and \(\triangleleft^2\) upgrades to \(\leftarrow\).

(a) If moreover \(\sqcup \ltimes U\) is \(\top\)-slice fully faithful, then \(\triangleleft^2\) upgrades to \(\cong\) and \(\triangleleft^3\) upgrades to \(\leftarrow\).

3. The symbols \(\triangleright_{i}\) upgrade under symmetric conditions.

Proof. 1. In the base category, it is clear that \(\mathbb{J}_{U'}^{\prime \Psi \ltimes \mathbf{y}J}\mathbb{J}_{J}^{\prime \Psi}\cong \Sigma^{\prime \nu_{1}}\mathbb{J}_{I}^{\prime \Psi \ltimes \mathbf{y}U}\mathbb{J}_{U}^{\prime \Psi}\). Applying the 2-functor \(\sqcup^{*}\) yields the commutation law for \(\forall\) and hence, by lemma 2.1.2, the general case.

43

|  \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \)  |
| --- | --- | --- | --- | --- | --- |
|  \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \) | \( \frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}}\frac{\partial\mathcal{A}_{0}}{\partial\mathcal{A}} \)  |

Figure 1: Commutation table for 2 multipliers (theorem 6.5.1).

44

2. We invoke theorem 6.3.1 with $\sigma = \pi_1 : \Psi \times \mathbf{y}J \to \Psi$. This yields

$$\Omega_{\mathbf{y}J}^{\Psi |} \mathbb{V}_{\mathbf{y}U}^{\Psi |} = \mathbb{V}_{\mathbf{y}U}^{\Psi \times \mathbf{y}J |} \Omega^{\pi_1 \ltimes \mathbf{y}U} : \widehat{\mathcal{V} / \Psi \ltimes \mathbf{y}U} \to \widehat{\mathcal{W} / \Psi \times \mathbf{y}J}.$$

Now $\pi_1 \ltimes \mathbf{y}U = \pi_1 \circ \nu_1^{-1}$ so we can rewrite this to

$$\Omega_{\mathbf{y}J}^{\Psi |} \mathbb{V}_{\mathbf{y}U}^{\Psi |} = \mathbb{V}_{\mathbf{y}U}^{\Psi \times \mathbf{y}J |} \Omega^{\nu_1^{-1} |} \Omega_{\mathbf{y}J}^{\Psi \ltimes \mathbf{y}U} : \widehat{\mathcal{V} / \Psi \ltimes \mathbf{y}U} \to \widehat{\mathcal{W} / \Psi \times \mathbf{y}J}.$$

The rest then follows by lemma 2.1.2.

(a) Also follows from the same invocation of theorem 6.3.1.

3. By symmetry.

## Acknowledgements

We thank Jean-Philippe Bernardy, Lars Birkedal, Daniel Gratzer, Alex Kavvos, Magnus Baunsgaard Kristensen, Daniel Licata, Rasmus Ejlers Møgelberg and Andrea Vezzosi for relevant discussions, and to the anonymous reviewers at LMCS for their valuable feedback. Special thanks to Dominique Devriese, whose pesky questions led to the current research.

## A Changelog

The first version of this technical report and the associated paper appeared in 2020. Since then, there have been significant changes, primarily terminological ones. To help out readers coming back to these texts after having consulted earlier versions (or associated presentations), we list the most important changes here.

### A.1 Definition 3.1.1

- **Unpointable** objects were formerly called **spooky**,
- **Not objectwise pointable** categories were formerly called **spooky**.

### A.2 Definition 3.1.2

- **Copointed** multipliers were formerly called **semicartesian**,
- Multipliers that are **comonads** were formerly called **3/4-cartesian**,
- **T-slice faithful** multipliers were formerly called **cancellative**,
- **T-slice full** multipliers were formerly called **affine**,
- **Not T-slice objectwise pointable** multipliers were formerly called **spooky**,
- **T-slice shard-free** multipliers were formerly called **connection-free**, and **shards** were formerly called **connections**,
- **T-slice right adjoint** multipliers were formerly called **quantifiable**.

### A.3 Definition 3.4.1

- A **morphism of copointed multipliers** was formerly called a **semicartesian** morphism of multipliers,
- A **comonad morphism of multipliers** was formerly called a **3/4-cartesian** morphism of multipliers.

45

## A.4 Quotient theorem

The **quotient theorem** was formerly called **kernel theorem**.

## A.5 Definition 3.5.1

**Slicewise** faithful / full / shard-free / right adjoint multipliers were formerly called **strongly** cancellative / affine / connection-free / quantifiable.

A previous version of paper and technical report featured only the now obsoleted definition of *indirect* shards/connections and slicewise *indirect* shard-freedom / strong *indirect* connection-freedom, that was based on the *indirect* boundary and *indirectly* dimensionally split morphisms. These notions are obsolete and are retained solely for consistency with [Nuy20, ch. 7]. The qualifier 'indirect' was only added a posteriori to distinguish with the more appropriate *direct* notions.

## A.6 Definition 4.1.1

**Presheafwise** faithful / full / shard-free / right adjoint multipliers were formerly called **providently** cancellative / affine / connection-free / quantifiable.

T-slice **elementally** faithful / full multipliers were formerly called **elementally** cancellative / affine.

A similar note as above applies to (in)direct shards/connections, shard/connection-freedom, boundaries and dimensional splitness.

## References

[BCH14] Marc Bezem, Thierry Coquand, and Simon Huber. A Model of Type Theory in Cubical Sets. In *19th International Conference on Types for Proofs and Programs (TYPES 2013)*, volume 26, pages 107–128, Dagstuhl, Germany, 2014. URL: http://drops.dagstuhl.de/opus/volltexte/2014/4628, doi:10.4230/LIPICS.TYPES.2013.107.

[BCM15] Jean-Philippe Bernardy, Thierry Coquand, and Guilhem Moulin. A presheaf model of parametric type theory. *Electron. Notes in Theor. Comput. Sci.*, 319:67 – 82, 2015. doi:http://dx.doi.org/10.1016/j.entcs.2015.12.006.

[BM20] Ales Bizjak and Rasmus Ejlers Møgelberg. Denotational semantics for guarded dependent type theory. *Math. Struct. Comput. Sci.*, 30(4):342–378, 2020. doi:10.1017/S0960129520000080.

[BT21] Simon Boulier and Nicolas Tabareau. Model structure on the universe of all types in interval type theory. *Math. Struct. Comput. Sci.*, 31(4):392–423, 2021. doi:10.1017/S0960129520000213.

[CCHM17] Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg. Cubical type theory: A constructive interpretation of the univalence axiom. *FLAP*, 4(10):3127–3170, 2017. URL: http://collegepublications.co.uk/ifcolog/?00019.

[Mou16] Guilhem Moulin. *Internalizing Parametricity*. PhD thesis, Chalmers University of Technology, Sweden, 2016. URL: publications.lib.chalmers.se/records/fulltext/235758/235758.pdf.

[ND18] Andreas Nuyts and Dominique Devriese. Degrees of relatedness: A unified framework for parametricity, irrelevance, ad hoc polymorphism, intersections, unions and algebra in dependent type theory. In *Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS 2018, Oxford, UK, July 09-12, 2018*, pages 779–788, 2018. doi:10.1145/3209108.3209119.

46

[ND24] Andreas Nuyts and Dominique Devriese. Transpension: The right adjoint to the Pi-type. CoRR (to appear in Logical Methods in Computer Science), abs/2008.08533, 2024. Version 4 (original version from 2020). URL: https://arxiv.org/abs/2008.08533, arXiv:2008.08533.

[nLa21a] nLab authors. adjoint functor, August 2021. [Online; consulted revision 107]. URL: http://ncatlab.org/nlab/show/adjoint%20functor.

[nLa21b] nLab authors. parametric right adjoint, August 2021. [Online; consulted revision 15]. URL: http://ncatlab.org/nlab/show/parametric%20right%20adjoint.

[nLa23a] nLab authors. locally. https://ncatlab.org/nlab/show/locally, February 2023. Revision 3.

[nLa23b] nLab authors. sieve. https://ncatlab.org/nlab/show/sieve, February 2023. Revision 49.

[Nuy18] Andreas Nuyts. Presheaf models of relational modalities in dependent type theory. CoRR, abs/1805.08684, 2018. arXiv:1805.08684.

[Nuy20] Andreas Nuyts. Contributions to Multimode and Presheaf Type Theory. PhD thesis, KU Leuven, Belgium, 8 2020. URL: https://anuyts.github.io/files/phd.pdf.

[Nuy23] Andreas Nuyts. Functor whose essential image is a cosieve? MathOverflow, 2023. (version: 2023-02-08). URL: https://mathoverflow.net/q/440372.

[NVD17] Andreas Nuyts, Andrea Vezzosi, and Dominique Devriese. Parametric quantifiers for dependent type theory. PACMPL, 1(ICFP):32:1–32:29, 2017. URL: http://doi.acm.org/10.1145/3110276, doi:10.1145/3110276.

[PK20] Gun Pinyo and Nicolai Kraus. From Cubes to Twisted Cubes via Graph Morphisms in Type Theory. In Marc Bezem and Assia Mahboubi, editors, 25th International Conference on Types for Proofs and Programs (TYPES 2019), volume 175 of Leibniz International Proceedings in Informatics (LIPIcs), pages 5:1–5:18, Dagstuhl, Germany, 2020. Schloss Dagstuhl–Leibniz-Zentrum für Informatik. URL: https://drops.dagstuhl.de/opus/volltexte/2020/13069, doi:10.4230/LIPIcs.TYPES.2019.5.

[Sta19] The Stacks Project Authors. Stacks project. http://stacks.math.columbia.edu, 2019. Tags 00VC and 00XF.

[XE16] Chuangjie Xu and Martin Escardó. Universes in sheaf models. Unpublished note, 2016. URL: https://cj-xu.github.io/notes/sheafuniverse.pdf.

47