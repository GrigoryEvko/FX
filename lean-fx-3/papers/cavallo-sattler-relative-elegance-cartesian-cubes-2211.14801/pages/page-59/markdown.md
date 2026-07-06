Relative Elegance and Cartesian Cubes with One Connection

59

Definition 7.17 (Cis06, §3.3.3, Proposition 4.2.23(a⇔b'') A functor u: C → D is aspheric if for every d ∈ D, the presheaf u*(&d) is aspheric.

An aspheric functor u: C → D between test categories induces a Quillen equivalence u* + u* between their test model structures [Cis06, Proposition 4.2.24]. For our purposes, the more relevant property is the following immediate consequence.

Proposition 7.18 (Cis06, Proposition 4.2.23(d)) Let u: C → D be an aspheric functor between two test categories. Then a map f in PSh(D) is a weak equivalence in D̅test if and only if u*f is a weak equivalence in C̅test.

Lemma 7.19 Any idempotent completion i: C → C̅ is aspheric.

Proof Any A ∈ C̅ is a retract of ia for some a ∈ C. Then i*& A is likewise a retract of i*& (ia) ≅ & a, thus aspheric by Corollary 4.51.

Lemma 7.20 ▲: Δ → D̅⊙ is aspheric.

Proof For any [1]ⁿ ∈ D̅⊙, we have ▲*& [1]ⁿ ≅ (Δ¹)ⁿ. As Δ is a strict test category [Mal05, Proposition 1.6.14], any finite product of representables in PSh(Δ) is aspheric [Cis06, Proposition 4.3.2(b)].

Lemma 7.21 A map f in PSh(D̅⊙) is a weak equivalence in D̅⊙⊙ if and only if ▲*f is a weak equivalence in Δ̅ᵏ.

Proof Any left Quillen equivalence both preserves (Ken Brown's lemma) and reflects [Hov99, Corollary 1.3.16] weak equivalences between cofibrant objects, so this follows from Corollary 7.7.

Theorem 7.22 The model structures D̅⊙test and D̅⊙⊙ are identical.

Proof As they have the same cofibrations, it suffices to show they have the same weak equivalences. This follows from Proposition 7.18 and Lemma 7.20 (together with Remark 7.14) and Lemma 7.21.

Corollary 7.23 The model structures D̅⊙test and D̅⊙⊙ are identical.

Proof Again, it suffices to show they have the same weak equivalences. By Proposition 7.18 and Lemma 7.19, a map f is a weak equivalence in D̅⊙test if and only if ■f is a weak equivalence in D̅⊙test. Likewise, f is a weak equivalence in D̅⊙⊙ if and only if ■f is a weak equivalence in D̅⊙⊙.

These results can also be read as characterizations of the fibrations in the test model structures:

2025/10/16 00:43