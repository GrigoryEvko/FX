CAVALLO, HÖFER

### 1.1 Outline

In Section 2, we recall some basic definitions, then observe that $\mathsf{FE}_{\mathcal{U}}$ holds if and only if the canonical map ceq-to-eq: $(A \cong B) \to (A \simeq B)$ is an equivalence for all $A, B: \mathcal{U}$, meaning that univalence quite literally factors into function extensionality and categorical univalence. In Section 3 we recall Von Glehn's polynomial model construction. The main technical contribution is Section 4, where we show that the polynomial model $\mathsf{Poly}(\mathbb{C})$ inherits $\mathsf{CUA}_{\mathcal{U}}^{\bullet}$ from the base model $\mathbb{C}$. In Section 5 we apply this result to a univalent base model to conclude that $\mathsf{ITT} + \mathsf{CUA}_{\mathcal{U}}^{\bullet} \not\vdash \mathsf{FE}_{\mathcal{U}}$. We discuss and compare other possible weakenings of $\mathsf{UA}_{\mathcal{U}}$ in Section 6, and finish with a review of related work in Section 7.

## 2 Decomposing univalence

Our basic theory ITT is Martin-Löf type theory with $\Sigma$ types, $\Pi$ types, intensional identity types, binary coproduct types, empty and unit types, and one universe $\mathcal{U}$ closed under all of these type formers.⁵ We use the term strict equality and symbol $\doteq$ for equality on the judgmental level; we use $=$ for identity types. We use $\cong$ for strict isomorphisms: two functions in opposite directions composing strictly to the identity. Note that $A \cong B$ is not a type, and $e: A \cong B$ is merely a shorthand for a meta-level assumption. Besides strict $\beta$ rules for all type formers, we include strict $\eta$ rules for $\Sigma$ types, $\Pi$ types, and the unit type.

For basic results, we cite Rijke's book [36], which does not introduce FE until Chapter 13; we only use results from earlier chapters. Crucially, we have basic facts about contractible types and that $\Sigma$ types respect equivalences in both arguments. Note that the analogous fact does not hold for $\Pi$ types absent FE. In contrast to Rijke [36], we assume the strict $\eta$ rule for $\Sigma$ types, not only for $\Pi$ types. This means, for example, that the equivalence witnessing the distributivity of $\Pi$ types over $\Sigma$ types is a strict isomorphism.

### 2.1 Univalent wild categories

The universe of ITT has the structure of an $(\infty, 1)$-category, with type of objects $\mathcal{U}_0 := \mathcal{U}$ and type of morphisms $\mathcal{U}_1(A, B) := (A \to B)$. The first layer of such an $(\infty, 1)$-categorical structure is captured by the Capriotti and Kraus' notion of wild category [11, Definition 4.1].

Definition 2.1 A wild category⁶ $\mathbb{C}$ is a type $\mathbb{C}_0$ and family of types $x, y: \mathbb{C}_0 \vdash \mathbb{C}_1(x, y)$ equipped with

- (i) composites $g \circ f: \mathbb{C}_1(x, z)$ for all $g: \mathbb{C}_1(y, z)$, $f: \mathbb{C}_1(x, y)$,
- (ii) identities $\mathrm{id}_x: \mathbb{C}_1(x, x)$ for all $x: \mathbb{C}_0$,
- (iii) associators $\alpha_{h,g,f}: h \circ (g \circ f) = (h \circ g) \circ f$ for all $h: \mathbb{C}_1(z, w)$, $g: \mathbb{C}_1(y, z)$, $f: \mathbb{C}_1(x, y)$, and
- (iv) unitors $\lambda_f: \mathrm{id}_y \circ f = f$ and $\rho_f: f \circ \mathrm{id}_x = f$ for all $f: \mathbb{C}_1(x, y)$.

If clear from context, we omit the subscripts when referring to the type of objects or family of morphisms. We write $x \to y$ for $\mathbb{C}_1(x, y)$ when $\mathbb{C}$ is clear, and we sometimes write $gf$ for $g \circ f$.

Example 2.2 As noted above, the universe $\mathcal{U}$ has a wild category structure with $\mathcal{U}(A, B) := (A \to B)$, composition and identities given by the usual composition of functions and identity functions, and reflexive equalities for the associators and unitors. More generally, for every type $I$ there is a wild category $\mathcal{U}^I$ whose objects are families $A: I \to \mathcal{U}$ and whose morphisms are indexed functions, $\mathcal{U}^I(A, B) := \prod_{i:I} A(i) \to B(i)$.

These wild categories are really strictly coherent $(\infty, 1)$-categories: the associators and unitors are strict equalities and satisfy all higher coherence laws (e.g., the pentagon) up to strict equality. All of the concrete wild categories we encounter in this article are of this kind.

Importantly, wild-categorical structure suffices to define isomorphism.

Definition 2.3 Given $s: x \to y$ and $r: y \to x$ in a wild category $\mathbb{C}$, we say that $r$ is a retraction of $s$ and $s$ is a section of $r$ if $rs = \mathrm{id}_x$. For a morphism $f$, we write $\mathsf{Sec}(f)$ and $\mathsf{Ret}(f)$ for the types of sections and retractions of $f$ respectively. We say $f$ is a $\mathbb{C}$-isomorphism if we have an element of the type $\mathsf{is-iso}_{\mathbb{C}}(f) := \mathsf{Sec}(f) \times \mathsf{Ret}(f)$ and write $x \cong_{\mathbb{C}} y$ for the type of isomorphisms between two objects $x, y: \mathbb{C}$.

⁵ There is no issue extending our results to multiple universes, but we only need one.

⁶ Capriotti and Kraus call this a wild precategory.

3