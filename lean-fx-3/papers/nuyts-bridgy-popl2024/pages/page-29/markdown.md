Internal and Observational Parametricity for Cubical Agda

8:29

be very close to that of the concurrent work by Altenkirch et al. [2024], who present an internally parametric type theory which avoids the use of an interval and validates the SRP definitionally.

## 6.2 Parametricity and Univalence

While relational parametricity requires functions to respect relations, HoTT asks that they respect equivalences. Of course, equivalences are a form of relations, so one idea is akin to the other.

We already mentioned Tabareau et al.'s [2021] work in the previous section. A reformulation of their work using our techniques would effectively lead to a shallow embedding of observational setoid [Pujet and Tabareau 2022] or homotopy [Altenkirch et al. 2022] type theory in a CwF of univalent setoids or groupoids.

Awodey et al. [2018] define Church-like encodings of ordinary but also higher inductive types in (homotopy) type theory. Since the correctness of the Church encoding relies on preservation not only of equivalences but of all relations, they cannot be proven correct in plain type theory or HoTT. Instead, the authors enforce relational parametricity simply by adding it as a 'such that' clause to the encoding.

## 6.3 The Structure Identity Principle (SIP)

We discuss appearances of the SIP in the literature and compare these to our discussion in Section 3. The HoTT book does not actually feature the full SIP and two other treatments rely on a DSL.

*Standard notions of structure on univalent categories.* The HoTT book [Program 2013] defines a *notion of structure* on a category $C$ essentially as a displayed category $\mathcal{D}^*$ over $C$ such that the projection functor $P : \Sigma C \mathcal{D}^* \to C$ from the total space is faithful, implying that the fiber of any object of $C$ (and its identity morphism) is a preorder. A notion of structure is *standard* if this preorder is always a partial order, which is defined as a univalent preorder. The theorem called SIP then states that if $C$ is univalent and $\mathcal{D}^*$ is standard, then the total space $\Sigma C \mathcal{D}^*$ is univalent. Relevant examples are group structures over h-sets, setoid structures over h-sets, monad structures over endofunctors, functor structures over indexed objects, ...

Fundamentally, the proof of this theorem does two things: It applies the extensionality principle for $\Sigma$-types to characterize a path between objects in $\Sigma C \mathcal{D}^*$, and it uses path induction to deduce 'displayed' univalence from standardness (which meant fiberwise univalence). Importantly, if $\mathcal{D}^*$ is quite complex, it is still up to the user to prove fiberwise univalence there, which still requires either rote work or the usage of a DSL for standard notions of structure. As such, we see this SIP as only a fragment of the fully general SIP.

*A DSL for univalent structures on Type.* Angiuli et al. [2021b] are concerned with proving the SIP (in our most general sense) for types of the form $T = \Sigma[X : \text{Type}] \Sigma[s : S X] P X s$, where $P X s$ is a mere proposition (h-prop). The idea is that a tuple $(X, s, p)$ is an algebra-like object with carrier $X$ and operations $s$ satisfying the axioms $P X s$. Their paper features a theorem titled SIP which amounts to the characterization of paths in a type of the form $\Sigma[X : \text{Type}] C X$. Since paths in a mere proposition can be characterized as informationless (Theorem 3.6), only the SIP for the operations type $S X$ remains to be dealt with. A DSL – essentially the type language of the STLC with base type $X$ (the carrier) – is then provided to build structures satisfying the SIP.

*A DSL for univalent higher categories.* Ahrens et al. [2020, thm. 7.10] use FOLDS [Makkai 1995] as a DSL for building univalent higher categories. In other words, they show that a higher type satisfies the SIP if it occurs as the object type of a higher category specified by a FOLDS signature.

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.