18–18

Semantics of multimodal adjoint type theory

represent its modality negatively, and use it as its own lock functor in semantics, thereby interpreting this instance of MATT in any topos equipped with such an endofunctor. Unfortunately, the intended model of [34] is an $(\infty, 1)$-topos without an evident 1-categorical analogue, so it is not covered by this paper.

Example 6.15 By [18, Theorem 8.1], there is a geometric morphism $S : \mathcal{E} \to \mathbf{sSet}$ from Johnstone's topological topos $\mathcal{E}$ to the topos $\mathbf{sSet}$ of simplicial sets, whose direct image $S_*$ is the total singular complex (suitably generalized) and whose inverse image $S^*$ is geometric realization. Since both $\mathcal{E}$ and $\mathbf{sSet}$ are local over $\mathbf{Set}$, this allows us to reason formally about geometric realization using an instance of MATT with three modes — say $t$ for the topological topos, $s$ for simplicial sets, and $d$ for discrete sets — with sinister coreflective adjunctions relating $d$ to both $t$ and $s$, and a sinister morphism $\sigma : s \to t$ for the geometric realization adjunction. As $\mathcal{E}$ is not cohesive (though $\mathbf{sSet}$ is), and geometric realization is not a right adjoint, this would be impossible without co-dextrification. Using [18, Theorem 8.2], we can do something similar for geometric realization of "simplicial spaces", i.e. simplicial objects of $\mathcal{E}$.

## 7 Conclusion and future work

We have shown that, contrary to appearances, general modal type theories formulated with "context locks" following [12,11] can be interpreted in diagrams of categories without requiring additional left adjoints to interpret the locks. This significantly expands the potential semantics of such theories, strengthening the argument that they are a good general approach to modal dependent type theories. In addition, we have formulated MATT, a general context-lock modal type theory that unifies the positive modalities of [12] with the negative ones of [11], and shown that it is the natural type theory to interpret in our semantics.

We have, however, left many open questions for future research, such as the following.

- (i) Can the assumption of $\kappa$-small limits be weakened, specifically when $\kappa > \omega$?
- (ii) It is known [39] that intensional dependent type theory can be interpreted in any $(\infty, 1)$-topos. Can intensional MATT be interpreted in any diagram of $(\infty, 1)$-topoi?
- (iii) Is there a full "internal language correspondence" relating MATT to suitable diagrams of categories? E.g. do adjoint modal natural models have a homotopy theory that presents diagrams of categories?
- (iv) Does MATT satisfy normalization, and which $(\mathcal{L}, \mathcal{S})$ are decidable? (See Remark 2.6.)
- (v) Is there a general modal dependent type theory using left multi-liftings, and can it be interpreted in the co-dextrification? Can it be generalized to cases where left multi-liftings do not exist?
- (vi) In [27], simple modal type theories were unified with substructural ones. Is there a context-lock approach to substructurality? Can it be unified with modal dependent type theory?

## References

[1] Annenkov, D., P. Capriotti, N. Kraus and C. Sattler, Two-level type theory and applications, Mathematical Structures in Computer Science (2023), p. 1–56. arXiv:1705.03307. URL https://doi.org/10.1017/S0960129523000130

[2] Awodey, S., Natural models of homotopy type theory, Math. Structures Comput. Sci. 28 (2018), pp. 241–286. arXiv:1406.3219. URL https://doi.org/10.1017/S0960129516000268

[3] Barwick, C. and P. Haine, Pyknotic objects, I. Basic notions (2019). Available online at https://doi.org/10.48550/arXiv.1904.09966

[4] Birkedal, L., R. Clouston, B. Manna, R. Ejlers Mogelberg, A. M. Pitts and B. Spitters, Modal dependent type theory and dependent right adjoints, Mathematical Structures in Computer Science 30 (2020), p. 118–138. arXiv:1804.05236. URL https://doi.org/10.1017/S0960129519000197

[5] Cavallo, E., "Higher Inductive Types and Internal Parametricity for Cubical Type Theory," Ph.D. thesis, Carnegie Mellon University (2021). Available online at https://www.cs.cmu.edu/~rwh/students/cavallo.pdf

[6] Dawson, R., R. Paré and D. Pronk, Adjoining adjoints, Adv. Math. 178 (2003), pp. 99–140. URL https://doi.org/10.1016/S0001-8708(02)00068-3