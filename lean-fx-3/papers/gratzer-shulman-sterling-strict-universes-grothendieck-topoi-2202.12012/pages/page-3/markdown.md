STRICT UNIVERSES FOR GROTHENDIECK TOPOI

3

and Streicher [HS97] that Grothendieck universes can be lifted pointwise into presheaf topoi, and it is slightly less well-known that sheafification preserves all the properties of this universe that do not involve strict equality of codes [Ber11; Str05]. Such a sheafified universe is already sufficient for nearly all mathematical purposes, but falls short in applications to the semantics and metatheory of dependent type theory, where certain strict laws not preserved by sheafification remain important.

In this paper we expose an alternative universe construction that applies in an arbitrary Grothendieck topos, using nothing but the cocompleteness and exactness properties of Grothendieck topoi. Ours is a variant of a construction of a universe of presheaves due to Shulman [Shu15]; we demonstrate that the resulting universe satisfies an important *realignment* property, which suffices in particular to obtain models of Martin-Löf type theory with a cumulative hierarchy of universes in any Grothendieck topos. The realignment condition is also an important ingredient in the construction of *univalent* universes for models of homotopy type theory [Uni13].

1.1. ELEMENTARY AXIOMS FOR UNIVERSES IN A TOPOS. Inspired by the definitions of classes of open and small maps from algebraic set theory, Streicher [Str05] has given a definition of a universe in an elementary topos $\mathcal{E}$ which we review in Definition 1.1.2 below.

1.1.1. NOTATION. Given morphisms $f: A \rightarrow B$ and $g: C \rightarrow D$, a morphism $\alpha: f \rightarrow g$ refers to a commuting square from $f$ to $g$:

$$\begin{array}{c} A \xrightarrow{\partial_0 \alpha} C \\ f \Biggl\downarrow \quad \alpha \quad \Biggl\downarrow g \\ B \xrightarrow{\partial_1 \alpha} D \end{array}$$

We shall also freely write $f \rightarrow g$ for an *anonymous* square from $f$ to $g$.

1.1.2. DEFINITION. A class of arrows $\mathcal{S} \subseteq \operatorname{Hom}_{\mathcal{E}}$ is called a universe by Streicher [Str05] when it satisfies the following axioms:

- (U1) $\mathcal{S}$ is *pullback-stable*, i.e. if $f \in \mathcal{S}$ and $g \rightarrow f$ is a cartesian square, then $g \in \mathcal{S}$.
- (U2) $\mathcal{S}$ contains all monomorphisms in $\mathcal{E}$.
- (U3) $\mathcal{S}$ is closed under composition.
- (U4) If $f: A \rightarrow I$ and $g: B \rightarrow A$ are in $\mathcal{S}$, then the pushforward $f_*g: B \rightarrow I$ lies in $\mathcal{S}$.
- (U5) There exists a generic morphism, i.e. a morphism $\pi: E \rightarrow U \in \mathcal{S}$ such that for any $f \in \mathcal{S}$ there exists a cartesian map $f \rightarrow \pi$.