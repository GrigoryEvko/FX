Cubical computational type theory

55

We likewise parameterize type systems by an interval context, separately specifying the value types available at each $\Psi$.

**Definition 3.1.14.** A *candidate type system* is a four-place relation $\tau$ relating interval contexts $\Psi$, values $V$ and $V'$ with free variables contained in $\Psi$, and value-coherent $\Psi$-PERs $R$.

**Notation 3.1.15.** Given a candidate type system $\tau$, we write $\tau \vDash \Psi \Vdash V \approx V' \downarrow R$ as syntactic sugar for $(\Psi, V, V', R) \in \tau$, and $\tau \vDash \Psi \Vdash V \downarrow R$ for $(\Psi, V, V, R) \in \tau$. Given a $\Psi$-PER $R$, we write $\tau[R]$ for the $\Psi$-relation $V \approx V' \in \tau[R]\langle \psi \rangle \iff \tau \vDash \Psi' \Vdash V \approx V' \downarrow R\psi$.

**Definition 3.1.16.** A candidate type system is a *type system* when it satisfies the following additional axioms.

- PER: For any fixed $\Psi$-PER $R$, $\tau[R]$ is a $\Psi$-PER.
- Unicity: If $\tau \vDash \Psi \Vdash V \approx V' \downarrow R$ and $\tau \vDash \Psi \Vdash V \approx V' \downarrow R'$, then $R = R'$.
- Value-coherence: For any fixed $R$, $\tau[R]$ is value-coherent.

We have analogues of the operators $Uni^+(-)$, $Sym^+(-)$, and $Trans^+(-)$ from Definition 2.1.25 defined pointwise in the context $\Psi$. Defining a similar operator for value-coherence, we can derive a condition analogous to Lemma 2.1.26 for checking that a candidate is a type system.

**Definition 3.1.17.** For any candidate $\tau$, we define a candidate type system $Coh^+(\tau)$ as follows: $Coh^+(\tau) \vDash \Psi \Vdash V \approx V' \downarrow R$ holds when $V \approx V' \in \Downarrow \tau[R]$ holds.

**Proposition 3.1.18.** Let $F$ be a monotone operator on candidate type systems such that $F(Sym^+(\mu F)) \subseteq Sym^+(\mu F)$, $F(Trans^+(\mu F)) \subseteq Trans^+(\mu F)$, $F(Uni^+(\mu F)) \subseteq Uni^+(\mu F)$, and $F(Coh^+(\mu F)) \subseteq Coh^+(\mu F)$. Then $\mu F$ is a type system.

### 3.1.3 Pretypes

Going forward, we assume a candidate type system $\tau$ and begin defining the judgments of type theory. We are not quite ready to define types; we still need to cut down to relations that support the coercion and composition operations. As it will usually take some work to prove that each type supports those operations, however, it is useful to introduce some intermediate notation. We therefore introduce a preliminary judgment, the *pretype* judgment, that does not require Kan operations. We can also define the element judgment at this stage; we do not need to know that a pretype supports the Kan operations to define what its elements are.