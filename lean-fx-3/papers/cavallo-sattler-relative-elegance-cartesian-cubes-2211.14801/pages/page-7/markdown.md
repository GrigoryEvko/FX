Relative Elegance and Cartesian Cubes with One Connection

7

accommodated in this way. However, the class of degree-preserving maps not admitting a lower-degree factorization must be closed under composition [Shu15, Theorem 8.13(ii)]. While u factors through no lower-dimensional object, uu factors through the 1-cube. As such, this generalization is unlikely to be helpful here.

## 1.2 Acknowledgments

We thank Steve Awodey, Thierry Coquand, and Emily Riehl, our collaboration with whom inspired this spin-off project, for their suggestions and feedback. We also thank Emily Riehl for alerting us to errors in the first preprint version of this article. The idea of embedding non-Reedy cube categories in larger Reedy categories came to us via Matthew Weaver and Daniel Licata, who experimented with (but did not ultimately use) this strategy in work on cubical models of directed type theory [WL20]. The first author thanks Brandon Doherty, Anders Mörtberg, Axel Ljungström, and Matthew Weaver for helpful conversations. We credit an observation of Imrich, Kalinowski, Lehner, and Piłśniak [IKLP14, Lemma 2] for inspiring the argument in Appendix A.2.2.

## 2 Background

### 2.1 Preliminaries

We begin by fixing a few notational conventions.

Notation 2.1 We write [E, F] for the category of functors from E and F. We write PSh(C) := [C^op, Set] for the category of presheaves on a category C and ∗: C → PSh(C) for the Yoneda embedding.

Notation 2.2 When regarding a functor as a diagram, we use superscripts for covariant indexing and subscripts for contravariant indexing. Thus if F: D → E then we have F^d ∈ E for d ∈ D, while if F: C^op → E then we have F_c ∈ E for c ∈ C. We sometimes partially apply a multi-argument functor: given F: C^op × D → E and c ∈ C, d ∈ D, we have F_c ∈ D → E, F^d ∈ C^op → E, and F_c^d ∈ E.

By a bifunctor we mean a functor in two arguments. We make repeated use of the Leibniz construction [RV14, Definition 4.4], which transforms a bifunctor into an bifunctor on arrow categories.

Definition 2.3 Given a bifunctor ⊙: C × D → E into a category E with pushouts, the Leibniz construction defines a bifunctor ⊖: C^→ × D^→ → E^→, with f ⊖ g defined for

2025/10/16 00:43