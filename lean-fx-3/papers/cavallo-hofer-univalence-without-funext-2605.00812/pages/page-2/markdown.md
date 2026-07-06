CAVALLO, HÖFER

equivalences between types $A, B$ is the type of homotopy bi-invertible maps, that is, $f: A \to B$ equipped with $s, r: B \to A$ such that $fs \sim \mathrm{id}_B$ and $rf \sim \mathrm{id}_A$ [36, §9.2]. We assume a fixed universe $\mathcal{U}$.

**Definition 1.1** *Function extensionality* (FE) is the principle that for every family of types $a: A \vdash B(a)$ and $f, g: \prod_{a:A} B(a)$, the map $(f =_{\prod_{a:A} B(a)} g) \to (f \sim g)$ is an equivalence. We write $\mathsf{FE}_{\mathcal{U}}$ for the relativization of FE to $\mathcal{U}$, i.e., its restriction to the case where $A: \mathcal{U}$ and $B: A \to \mathcal{U}$.

**Definition 1.2** *Univalence* ($\mathsf{UA}_{\mathcal{U}}$) is the principle that the map id-to-eq: $(A =_{\mathcal{U}} B) \to (A \simeq B)$ is an equivalence for all $A, B: \mathcal{U}$.

Dorais observed essentially that the map id-to-eq: $(A =_{\mathcal{U}} B) \to (A \simeq B)$, which sends the reflexive path to the identity equivalence, factors up to homotopy through an intermediate type

$$(A =_{\mathcal{U}} B) \xrightarrow{\text{id-to-eq}} (A \cong B) \xrightarrow{\text{ceq-to-eq}} (A \simeq B)$$

of what we call *categorical equivalences*: maps $f: A \to B$ equipped with $s, r: B \to A$ such that $fs =_{B \to B} \mathrm{id}_B$ and $rf =_{A \to A} \mathrm{id}_A$, i.e., with left and right inverses up to equality rather than homotopy. This suggests Dorais' proposed weakening of univalence:

**Definition 1.3** *Categorical univalence* ($\mathsf{CUA}_{\mathcal{U}}$) is the principle that id-to-ceq: $(A =_{\mathcal{U}} B) \to (A \cong B)$ is an equivalence for all $A, B: \mathcal{U}$.

The type $A \cong B$ can be described as the type of isomorphisms from $A$ to $B$ in the *wild category* of types in $\mathcal{U}$ and functions between them. $\mathsf{CUA}_{\mathcal{U}}$ states exactly that $\mathcal{U}$ is a univalent wild category. In the presence of function extensionality in $\mathcal{U}$, the map $(A \cong B) \to (A \simeq B)$ is an equivalence, and so $\mathsf{FE}_{\mathcal{U}} + \mathsf{CUA}_{\mathcal{U}}$ implies $\mathsf{UA}_{\mathcal{U}}$; conversely, the fact that $\mathsf{UA}_{\mathcal{U}}$ implies $\mathsf{FE}_{\mathcal{U}}$ means that it also implies $\mathsf{CUA}_{\mathcal{U}}$. Dorais asked whether the converse is true: does $\mathsf{CUA}_{\mathcal{U}}$ imply $\mathsf{UA}_{\mathcal{U}}$, or equivalently $\mathsf{FE}_{\mathcal{U}}$?

We answer this question in the negative, identifying a model of ITT with a universe that validates $\mathsf{CUA}_{\mathcal{U}}$ but not $\mathsf{FE}_{\mathcal{U}}$. Actually, we prove the consistency of $\neg \mathsf{FE}_{\mathcal{U}}$ with a slightly stronger statement:

**Definition 1.4** *Familial categorical univalence* ($\mathsf{CUA}_{\mathcal{U}}^{\bullet}$) is the principle that for all $I: \mathcal{U}$, the wild category $\mathcal{U}^I$—whose objects are families $A: I \to \mathcal{U}$ and whose morphisms $A \to B$ are families of functions $\prod_{i:I} A(i) \to B(i)$—is a univalent wild category.

We assume strict $\eta$ laws for unit and $\Pi$ types, so $\mathsf{CUA}_{\mathcal{U}}^{\bullet}$ implies $\mathsf{CUA}_{\mathcal{U}}$ by taking $I = 1$. We show the independence of $\mathsf{CUA}_{\mathcal{U}}^{\bullet}$ from $\mathsf{FE}_{\mathcal{U}}$ using Von Glehn's *polynomial model* construction $\mathbf{Poly}(-)$ [50,33], a known source of models of type theory that refute function extensionality. Specifically, we prove:

**Theorem 1.5 (4.17)** *Let $\mathbb{C}$ be a model of ITT with extensive finite coproducts of types satisfying the strict $\eta$ rule. If $\mathbb{C} \models \mathsf{CUA}_{\mathcal{U}}^{\bullet}$, then $\mathbf{Poly}(\mathbb{C}) \models \mathsf{CUA}_{\mathcal{U}}^{\bullet}$.*

Familial categorical univalence arises naturally in the construction: just to show $\mathbf{Poly}(\mathbb{C}) \models \mathsf{CUA}_{\mathcal{U}}$, we already require $\mathbb{C} \models \mathsf{CUA}_{\mathcal{U}}^{\bullet}$. Function extensionality always fails in polynomial models [50, §4.5], so it remains to provide a suitable input model. Off-the-shelf cubical and simplicial models of homotopy type theory will do, as Moss and Von Glehn have already observed [33, §6]. We conclude:

**Theorem 1.6 (5.6)** $\mathsf{ITT} + \mathsf{CUA}_{\mathcal{U}}^{\bullet} \not\models \mathsf{FE}_{\mathcal{U}}$.

Part of the appeal of weak foundations is that they allow us to tease apart the components of mathematics. Each type former of Martin-Löf's type theory has a distinct, well-defined purpose. Univalence fits in uneasily in this picture. While it has beautiful consequences, it also has *many* consequences, and—like impredicativity or the law of the excluded middle—it may be hiding finer structure beneath its surface.

By scratching at that surface, we hope to understand what makes univalence tick. The polynomial model offers some motivation and a testing ground for weaker forms of the axiom. We are left with more questions than answers; unlike in the case with FE, where superficial variations on univalence usually turn out to be equivalent, here we find subtly distinct axioms with no canonical choice among them. Still, we hope our results can provoke further reflection on the foundations of homotopy type theory.

2