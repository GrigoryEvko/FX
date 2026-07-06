Cubical computational type theory 63

- $V \approx V' \in R\langle\psi\rangle$ holds for $\Psi' \Vdash \psi \in \Psi$ exactly when one of the following holds:

- $r\psi = 0$, and $V \approx V' \in S\psi$,
- $r\psi = 1$, and $V \approx V' \in T\psi$,
- $r\psi = x$, and $V = v_x(M, P)$ and $V' = v_x(M', P')$ with $M \approx M' \in \Downarrow S\psi$, $P \approx P' \in \Downarrow T\psi$, and $(\text{fst}(I\psi)) M \approx P \in \Downarrow T\psi$, where in the final equation we regard $T\psi$ as a $(\Psi', x \equiv 0)$-PER by weakening.
- Clauses for dependent products and composites of types. The first two are pointwise extensions of the clauses in Example 2.1.27, as with function types above. For composites of types, see [Ang19, Figure 4.3, Section 4.4.11].

We define the candidate type system $\tau_0$ to be the least fixed point of $F$.

In order for $F$ to be a genuine operator on candidate type systems, it must be the case that the $\Psi$-relations it assigns to each value type are actually value-coherent $\Psi$-PERs. This is most easily seen to be true as a corollary of the introduction rules for each type's relation, so we defer the proof for the moment. Similarly, the condition on $Coh^*(-)$ required by Proposition 3.1.18, which we need to see that the fixed-point is a type system, will be a consequence of the formation rules for each type in $F_0(\tau)$. The unicity and PER conditions, on the other hand, are as straightforward as before.

Example 3.1.33 (Type system with one universe). We can define a type system with a universe by following the recipe of Example 2.1.29. For a candidate $\tau$, we define a candidate $U(\tau)$ by declaring that that $U(\tau) \models \Psi \Vdash V \approx V' \downarrow R$ holds when $V = V' = U$ and $R$ is the $\Psi$-relation $W \approx W' \in R\langle\psi\rangle \iff \exists S. \tau \models \Psi' \Vdash W \approx W' \downarrow S$ for $\Psi' \Vdash \psi \in \Psi$. Our candidate type system with a universe, $\tau_1$, is then the fixed point of $\tau \mapsto F(\tau) \cup U(\tau_0)$.

### 3.1.6 Rules for cubical type theories

Taking $\tau_0$ and $\tau_1$ as our prototypical (candidate) type systems, we now build up an edifice of rules associated to each type. This is a more difficult task than for pure Martin-Löf type theory because of the demands of coherent evaluation: to show that some term belongs to a type, we have to analyze its behavior under iterated applications of interval substitution and evaluation. Fortunately, we can at least factor the results through a collection of more intuitive lemmas, so that we need not interact with the definition of $\Downarrow-$ directly.

First, the following lemma can be used to show that a pair of values in some $R$ belongs also to $\Downarrow R$: it suffices to show that every substitution instance belongs either to $R$ or to $\Downarrow R$. Often, while the terms themselves are values, but some substitutions cause them to become non-values already known to belong to $\Downarrow R$.