Outlook 155

# **inductive Ex where**

| a ∈ Ex
| b(t : Ex) ∈ Ex
| c(n : Nat, f : Nat → Ex, p : T_zero, q : T_suc, x : I) ∈ Ex [x ≡ 0 ↔ a | x ≡ 1 ↔ f n]

Our own schema therefore includes a type satisfying the induction principle of Lumsdaine and Shulman's type.

**Identity types** A primary motivation for constructing indexed inductive types in cubical type theory is to obtain an identity type. As discussed in Section 5.3, while the Path type is a suitable replacement for Id in most regards, it does not satisfy the same J principle—there is a term with the type of J for path types (Lemma 3.2.3), but it does not validate an exact reduction principle on reflexive paths. This failure is explored in detail by Swan [Swa18b].

An alternative construction is therefore necessary to realize identity types in cubical type theory, and in particular to show that cubical type theory interprets **HoTT**. Swan [Swa18a] presents one technique, using the cofibration-trivial fibration factorization of a model structure to obtain identity types from path types; this construction applies in the various structural cubical sets models as well as affine cubical sets. Cohen, Coquand, Huber, and Mörtberg define identity types whose elements are cubical paths paired with constraints on which they are guaranteed reflexive [CCHM15, §9.1]; this construction is also possible in a cartesian setting [ABCFHL19, §2.16], and is analyzed by Swan as a simplified special case of his construction [Swa18a, §6]. Our own construction is distinct from these. In [Cav19], a model-categorical reformulation is presented; it relies instead on a trivial cofibration-fibration factorization and resembles van den Berg and Garner's interpretation of identity types in simplicial sets and related settings [BG12].

## 7.2 Outlook

We have developed a full-featured schema for higher inductive types in cartesian cubical type theory, complete with a computational interpretation. Our specification grammar accommodates almost all features that appear in the **HoTT** book [Uni13] and subsequent work in homotopy and cubical type theory, including recursive path constructors, recursive arguments of function and path types in the type being constructed, and indices. We expect that similar schemata could now be straightforwardly developed in De Morgan cubical type theory [CCHM15] or Cavallo, Mörtberg, and Swan's minimal cubical type theory [CMS20], taking their examples of higher inductive constructions and generalizing following the pattern developed here. It seems safe to say at this point that the