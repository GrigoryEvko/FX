4

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

The axioms of Definition 1.1.2 ensure the closure of $\mathcal{S}$ under several type theoretic operations, if we view an element $f: A \rightarrow B \in \mathcal{S}$ as a dependent type $x: B \vdash A[x]$. Then (U1) corresponds to the substitution action for dependent types and terms; (U2) states that all propositions are small; (U3-4) provide for dependent sums and dependent products, and (U5) provides a generic dependent type $x: U \vdash E[x]$ of which every other dependent type in $\mathcal{S}$ is a substitution instance.

In the type-theoretic literature, it is the base of this family $U$ which is called the universe and the generic family is the dependent type $\mathsf{EI}$ rendering an element of this universe as a genuine type. We occasionally adopt this terminology and blur the distinction between a universe and its generic map by referring to $E \rightarrow U$ simply as a universe. Some caution is required: while a generic map uniquely determines a universe, the converse is not necessarily true and a universe can have multiple distinct generic maps.

In the context of Martin-Löf type theory, it is common to study classes of maps that may not satisfy all the axioms above; for instance, type theory is often used in settings that do not have a single well-behaved notion of proposition, so (U2) loses some significance. We therefore define a notion of *pre-universe* below.

### 1.1.3. DEFINITION. A pre-universe is a class of arrows satisfying axioms (U1, U3-5).

Streicher [Str05] discusses some additional useful but optional axioms for universes.

(U6) (Propositional subuniverse) $\mathcal{S}$ contains the terminal map $\Omega \rightarrow \mathbf{1}_{\bar{k}}$.^1

(U7) (Descent) If $g \in \mathcal{S}$ and $g \rightarrow f$ is a cartesian epimorphism, then $f \in \mathcal{S}$.

A Grothendieck universe $\mathsf{V}$ in $\mathbf{Set}$ is readily seen to induce a universe $\mathcal{S}_{\mathsf{V}}$ in the sense of Definition 1.1.2 where $\mathcal{S}_{\mathsf{V}}$ consists of the collection of maps with $\mathsf{V}$-small fibers. Hofmann and Streicher [HS97] and Streicher [Str05] have shown that $\mathcal{S}_{\mathsf{V}}$ can be lifted systematically to presheaves and sheaves. The first result in particular has been widely used in the semantics of type theory, because the generic morphism satisfies a number of strict equations specific to its construction. These additional equations are crucial for modeling *e.g.* strict cumulative universes. Other more novel applications of this strictness have emerged in models of Voevodsky's univalence axiom and homotopy type theory. Only more recently has an axiomatic basis for these stricter Hofmann–Streicher universes been isolated:

### 1.1.4. DEFINITION. A universe $\mathcal{S}$ is said to have realignment with respect to a class $\mathcal{M}$ of monomorphisms when axiom (U8) below is satisfied:^2

(U8) A chosen cartesian morphism $h \rightarrow \pi$ into the generic morphism can be extended along any cartesian monomorphism $h \mapsto f$ lying horizontally over an element of $\mathcal{M}$

^1 Streicher [Str05] refers to this property as impredicativity, but we wish to avoid confusion with a different notion of impredicativity that involves the existence of dependent products along maps *not* in $\mathcal{S}$, which has its prototype in the full internal subcategory of the category of assemblies spanned by modest sets [Hyl88; HRR90; Str17].

^2 Our axiom (U8) is denoted (2') by Shulman [Shu15].