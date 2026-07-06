22 Martin-Löf's type theory

**Notation 2.1.6.** Given a candidate type system $\tau$, we write $\tau \vDash V \approx V' \downarrow R$ as syntactic sugar for $(V, V', R) \in \tau$, and $\tau \vDash V \downarrow R$ for $(V, V, R) \in \tau$. We write $\tau[R]$ for the binary relation $\tau \vDash (-) \approx (-) \downarrow R$, which relates types when they are equated by $\tau$ with interpretation $R$.

We read an instance $\tau \vDash V \approx V' \downarrow R$ of the relation as asserting that $V$ and $V'$ are equal type names in $\tau$ and that their elements are defined by the PER $R$: $W \approx W' \in R$ means that $W$ and $W'$ are equal elements of the type named by $V$ (or $V'$).

**Definition 2.1.7.** A candidate type system is a *type system* when it satisfies the following additional axioms.

- *PER*: For any fixed PER $R$, the relation $\tau[R]$ is a partial equivalence relation.
- *Unicity*: If $\tau \vDash V \approx V' \downarrow R$ and $\tau \vDash V \approx V' \downarrow R'$, then $R = R'$.

The former ensures that value type equality is a partial equivalence relation; the latter ensures that each type name has at most one interpretation as a relation.

### 2.1.3 Typing judgments

Given an operational semantics and candidate type system $\tau$, we derive an interpretation of the typing judgments in two stages: first, we extend the type system to closed terms that may not be values, then to open terms. The status of non-value closed terms is determined by evaluating them: if terms evaluate to equal values, then they are equal terms.

**Definition 2.1.8.** Let $R$ be a relation. We define a relation $\Downarrow R$ as follows: $M \approx M' \in \Downarrow R$ holds when there exist values $V, V'$ such that $M \Downarrow V, M' \Downarrow V'$, and $V \approx V' \in R$.

**Definition 2.1.9 (Closed judgments).**

- *Closed types*: $\Vdash A = A'$ type is defined to hold when $A \approx A' \in \Downarrow \tau[R]$ for some $R$.
- *Closed terms*: $\Vdash M = M' \in A$ is defined to hold when $A \in \Downarrow \tau[R]$ for some $R$ such that $M \approx M' \in \Downarrow R$.

The unary judgment $\Vdash A$ type is shorthand for $\Vdash A = A$ type. Likewise, $\Vdash M \in A$ is shorthand for $\Vdash M = M \in A$.

Both types and terms are programs: a type is simply a program that computes the name of a value type (as specified by the type system). Note that if $\Vdash M \in A$ and $M \Downarrow V$, we always have $\Vdash M = V \in A$.