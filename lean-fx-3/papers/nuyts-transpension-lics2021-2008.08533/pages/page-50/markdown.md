16:50

A. NUYTS AND D. DEVRIESE

Vol. 20:2

- We need to decide equality of 2-cells. Solutions may exist in the literature on higher-dimensional rewriting. Alternatively, we need to extend MTT with a language to reason about 2-cell equality [Nuy23b].
- The substitution modality should ideally reduce like ordinary substitution. Remark 5.5 explores what is needed for this to work.
- We need a syntax-directed way to close the section computation rules of $\Phi$ (Fig. 10) and transpension elimination (Section 9) under substitution, but see Remark 9.4.
- We need to be able to decide whether the boundary predicate, or any similar predicate about shape variables such as $i \equiv_1 0$ in cubical type theory, is true. This problem has been dealt with in special cases, e.g. in implementations of cubical type theory [VMA19].

Applications include all applications (discussed in Section 1) of the presheaf internalization operators recovered from the transpension type in Section 10. Moreover, our modal approach to shape variables via multipliers allows the inclusion of Pinyo and Kraus's twisted prism functor [PK20] as a semantics of an interval variable, which we believe is an important advancement towards higher-dimensional directed type theory.

# ACKNOWLEDGEMENTS

We thank Jean-Philippe Bernardy, Lars Birkedal, Daniel Gratzer, Alex Kavvos, Magnus Baunsgaard Kristensen, Daniel Licata, Rasmus Ejlers Møgelberg and Andrea Vezzosi for relevant discussions, and the anonymous reviewers for their feedback which has been a great guidance in improving the clarity of this paper.

# APPENDIX A. CHANGELOG

The first preprint of this paper appeared in 2020 and is subsumed in [Nuy20a, ch. 7]. Since then, there have been significant changes, primarily terminological ones. To help out readers coming back to this paper after having consulted earlier versions (or associated presentations), we list the most important changes here.

# A.1. Terminology.

# A.1.1. Definition 6.2.

- **Copointed** multipliers were formerly called **semicartesian**,
- Multipliers that are **comonads** were formerly called **3/4-cartesian**,
- **T-slice faithful** multipliers were formerly called **cancellative**,
- **T-slice full** multipliers were formerly called **affine**,
- **T-slice shard-free** multipliers were formerly called **connection-free**, and **shards** were formerly called **connections**,
- **T-slice right adjoint** multipliers were formerly called **quantifiable**.

# A.1.2. Definition 6.4.

- **Unpointable** objects were formerly called **spooky**,
- **Not objectwise pointable** categories were formerly called **spooky**.