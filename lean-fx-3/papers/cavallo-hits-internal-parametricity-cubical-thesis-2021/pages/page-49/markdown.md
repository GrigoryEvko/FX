A logic of programs 37

# **Rules 2.1.43 (Formation and introduction for identity types).**

$$\frac{\text{FORMATION}}{\vdash A = A' \text{ type} \quad \vdash M_0 = M_0' \in A \quad \vdash M_1 = M_1' \in A}$$
$$\vdash \text{Id}(A, M_0, M_1) = \text{Id}(A', M_0', M_1') \text{ type}$$

$$\frac{\text{INTRODUCTION}}{\vdash A \text{ type} \quad \vdash M = M' \in A}$$
$$\vdash \text{refl}(M) = \text{refl}(M') \in \text{Id}(A, M, M')$$

One elimination principle for identity types, historically known as the “J rule” after Martin-Löf, expresses the inductive generation of the family of identity types by the refl constructor. When we have a property $a_0 : A, a_1 : A, p : \text{Id}(A, a_0, a_1) \gg B$ type dependent on pairs of terms and identities between them, it suffices to prove it in the case that the identity is refl.

# **Rules 2.1.44 (Elimination for identity types).**

$$\frac{\text{ELIMINATION}}{\vdash M_1 \in A \quad a_0 : A, a_1 : A, p : \text{Id}(A, a_0, a_1) \gg B = B' \text{ type} \quad \vdash M_0 \in A \quad \vdash P = P' \in \text{Id}(A, M_0, M_1) \quad a : A \gg N = N' \in B[a/a_0, a/a_1, \text{refl}(a)/p]}$$
$$\vdash \text{elim}_{\text{Id}}(a_0, a_1, p, B, P, a, N) = \text{elim}_{\text{Id}}(a_0, a_1, p, B', P', a, N') \in B[M_0/a_0, M_1/a_1, P/p]$$

$$\frac{\text{REDUCTION}}{\vdash M \in A \quad a : A \gg N \in B[a/a_0, a/a_1, \text{refl}(a)/p]}$$
$$\vdash \text{elim}_{\text{Id}}(a_0, a_1, p, B, \text{refl}(M), a, N) = N[M/a] \in B[M/a_0, M/a_1, \text{refl}(M)/p]$$

Although the J rule captures the inductive generation of the identity family by the refl constructor, it is actually a fairly weak principle. In particular, it does not suffice to show that proofs of identities are unique: that for any $P, Q \in \text{Id}(A, M_0, M_1)$, there exists some $T \in \text{Id}(\text{Id}(A, M_0, M_1), P, Q)$. This principle is nonetheless true in the computational semantics—indeed, we have $\text{refl}(P) \in \text{Id}(\text{Id}(A, M_0, M_1), P, Q)$. The semantics validates the much stronger *equality reflection* rule, which turns elements of identity types into judgmental equalities.

# **Rule 2.1.45 (Equality reflection).**

$$\frac{\vdash M_0 \in A \quad \vdash M_1 \in A \quad \vdash P \in \text{Id}(A, M_0, M_1)}{\vdash M_0 = M_1 \in A}$$