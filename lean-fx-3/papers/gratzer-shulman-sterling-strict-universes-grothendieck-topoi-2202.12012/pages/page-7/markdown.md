STRICT UNIVERSES FOR GROTHENDIECK TOPOI

7

also produces universes of sheaves satisfying (U1–6), as the sheafification of the generic small family of presheaves is generic for small families of sheaves.

**Section 3.** We review a number of categorical preliminaries to our main result involving descent and $\kappa$-compactness.

**Section 4.** Adapting a construction of Shulman [Shu15], we prove our main result (Corollary 4.3.3): the universe of relatively $\kappa$-compact sheaves for a strongly inaccessible cardinal $\kappa$ satisfies all the universe axioms including (U8). We deduce that cumulative hierarchies of strict universes lift from **Set** to any Grothendieck topos.

**Section 5.** We discuss and compare two equivalent formulations of the realignment property employing the internal language of a topos.

**Section 6.** The results of Section 4 have important consequences for the syntax and semantics of type theory; we review a few of these applications in Section 6. For instance, we have already shown that (U8) is sufficient to construct strictly cumulative hierarchies of universes, and with the existence of these hierarchies in arbitrary Grothendieck topoi the independence of several logical principles of Martin-Löf type theory immediately follows; contrary to some claims, sheaf semantics is sufficient and there is no need to move from sheaves to stacks. We outline applications to independence results in Section 6.1.

We also illustrate the general utility of (U8) through two specific examples: the semantics of univalence in homotopy type theory (Section 6.2) and the construction of glued models of type theory (Section 6.3) for proving syntactic metatheorems such as canonicity, normalization, and decidability. In both cases, (U8) allows us to leverage existing categorical machinery while still maintaining the required strict equations.

**FOUNDATIONAL ASSUMPTIONS.** Throughout, we work in a sufficiently strong metatheory to ensure that **Set** comes equipped with a collection of universes *e.g.*, ZFC with the Grothendieck universe axiom; we make use of the axiom of choice. We return to this topic briefly in Section 7.1.

**Acknowledgments** We are grateful to Steve Awodey, Thomas Streicher, and the anonymous referees for helpful feedback and corrections to an earlier draft of this paper. This research was supported by the United States Air Force Office of Scientific Research under award numbers FA9550-21-1-0009 and FA9550-23-1-0728 (Tristan Nguyen, program officer).

## 2. Reviewing Hofmann and Streicher’s universes

We begin by recalling constructions from Hofmann and Streicher [HS97] and Streicher [Str05] lifting universes from **Set** to Grothendieck topoi. To begin with, fix a *Grothendieck universe* $\mathsf{V}$, a transitive non-empty set closed under Kuratowski pairing, power-sets, and $I$-indexed unions for each $I \in \mathsf{V}$.

2.1. UNIVERSES OF SETS. Each Grothendieck universe defines a universe as in Definition 1.1.2.