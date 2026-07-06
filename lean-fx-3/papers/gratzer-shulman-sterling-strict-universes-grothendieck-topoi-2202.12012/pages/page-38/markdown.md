38

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

The benefit of the present axiomatization is that a family of types being fiberwise $J$-connected is a *property*; in contrast, the Orton–Pitts axiomatization (Definition 5.1.3) requires every use of realignment to be accompanied by a chosen isomorphism. We have gained significant experience with both axiomatizations in the context of synthetic Tait computability [Gra22; Niu+22; Ste21; SA21; SH21; SH22], and found that the present one is substantially simpler to use in practice.

## 6. Applications of realignment

An immediate consequence of Section 4 is an interpretation of Martin-Löf type theory with a cumulative hierarchy of universes in arbitrary Grothendieck topoi (recall that we have assumed a hierarchy of Grothendieck universes). In fact, the new interpretation of Martin-Löf type theory in Grothendieck topoi enables more direct independence proofs for various axioms such as Markov's principle. But the realignment property itself has played an important role in the semantics of homotopy type theory as developed by Awodey [Awo21], Kapulkin, Lumsdaine, and Voevodsky [KL21], Shulman [Shu15; Shu19], Stenzel [Ste19], and Streicher [Str14]. In particular, realignment appears to be a necessary ingredient for constructing a fibrant and univalent universe. The same principle is employed by Sterling, Angiuli, and Gratzer [SAG22, Lemma 5.33] in their proof of *canonicity* for XTT, a variant of cubical type theory: in particular, *op. cit.* used a special case of (U8) to realign codes in the universe of an Artin gluing over chosen codes in the universe of its open subtopos.

### 6.1. INDEPENDENCE RESULTS FOR MARTIN-LÖF TYPE THEORY.

Sheaf semantics has historically been employed to prove independence results for various forms of logic; the use of sheaf semantics to verify the analogous results for dependent type theory with universes has been hampered by the (now-resolved) difficulties in constructing well-behaved universes in sheaf topoi. These difficulties have motivated two somewhat less direct methods for proving independence results: constructing *operational* or *relational* models of type theory using the Beth–Kripke–Joyal sheaf semantics of predicate logic [CM16], or by constructing denotational models of type theory in *stacks* rather than sheaves [CMR17]. The present work provides a more direct approach, as the presence of universes validating (U1–8) ensures a simple and direct denotational semantics of dependent type theory in sheaves. We illustrate this through a concrete example and sketch a simpler proof of the independence of Markov's principle.

#### 6.1.1. INDEPENDENCE OF MARKOV'S PRINCIPLE.

Markov's principle states that for any decidable property $P(x)$ of natural numbers, the proposition $\exists x.Px$ is $\neg\neg$-stable:

$$\forall P : \mathbb{N} \rightarrow \mathbf{2}.\neg\neg\exists x.Px = 0 \rightarrow \exists x.Px = 0$$

Formalized in the language of dependent type theory, Markov's principle is rendered by Coquand and Manna [CM16] equivalently as the existence of a global element of the following type:

$$\prod_{P:\mathbb{N}\rightarrow\mathbf{2}} (\neg\neg\sum_{x:\mathbb{N}} Px = 0 \rightarrow \sum_{x:\mathbb{N}} Px = 0)$$