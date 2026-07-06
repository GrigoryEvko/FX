A logic of programs 31

**Proposition 2.1.30.** $\tau_1$ is a value type system.

Both $\tau_1$ and its universe U will be closed under functions, products, and identity types and contain natural numbers, unit, and empty types; the universe does not of course contain itself. As demonstrated in [Ang19, §2.2], we could repeat this process to define type systems $\tau_n$ with $n$ universes, and ultimately a type system $\tau_\omega := \bigcup_n \tau_n$ with an infinite hierarchy of universes $U_0 \in U_1 \in U_2 \in \cdots$. For our purposes, a single universe is sufficient, so we satisfy ourselves with $\tau_1$.

*Remark 2.1.31.* In the case that a monotone operator $F$ on a complete lattice is *Scott-continuous*—that is, preserves directed sets—its fixed point may be characterized as the union of the sequence $\emptyset \subseteq F(\emptyset) \subseteq F^2(\emptyset) \subseteq \cdots$ [Sco72]. The operator $F$ used in Example 2.1.27 is not continuous, however, as a counterexample observed by Harper demonstrates [Har92, Theorem 7.1]. Consider the following type.

$$A := (n : \text{Nat}) \rightarrow \text{elim}_{\text{Nat}}(\dots U; n; \text{Nat}, \dots B.B \times \text{Nat})$$

This is the type of functions that, for every natural number $n$, returns an element of the $(n+1)$-fold product of Nat. For each $n \in \mathbb{N}$, the candidate type system $F^n(\emptyset)$ for $F$ defined in Example 2.1.27 only contains the $k$-fold product of Nat for every $k \leq n$, so the union $\bigcup_{n \in \mathbb{N}} F^n(\emptyset)$ does not contain $A$. The least fixed point of $F$, on the other hand, *does* contain this type.

## 2.1.5 Rules for type and term formers

We now take a look at the specific properties of $\tau_0$ and $\tau_1$, namely the types that they support. The rules we check for each type follow a general pattern we will see repeated across every type former we introduce in this thesis: there are *formation*, *introduction*, *elimination*, *reduction*, and (possibly) *uniqueness* rules.

### 2.1.5.1 Functions

To start with, let us consider function types, which we have included in both $\tau_0$ and $\tau_1$. Our first rule, formation, gives conditions under which a function type is well-formed. For this rule and for all subsequent rules, we give a proof for the case where the conclusion is a closed judgment. The rule for open judgments then follows by applying the closed rule pointwise, as in the derivation of Rules 2.1.15 from Rules 2.1.13 above.

**Rule 2.1.32 (Function formation).**

$$\frac{\Vdash A = A' \text{ type} \quad a : A \gg B = B' \text{ type}}{\Vdash (a : A) \rightarrow B = (a : A') \rightarrow B' \text{ type}}$$