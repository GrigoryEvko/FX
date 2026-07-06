Cubical computational type theory 53

### 3.1.2 Operational semantics and type systems

The two defining components of a cubical type theory—its operational semantics and its type system—must take an ambient interval context into account. For the operational semantics, this just means that the judgments operate on terms that may contain interval variables.

**Definition 3.1.5.** An *operational semantics* is a definition of two judgments $M$ val and $M \longmapsto N$ operating on terms that contain only interval variables, satisfying the following properties.

- **Determinism:** If $M \longmapsto N$ and $M \longmapsto N'$, then $N = N'$. For any $M$, it is not the case that both $M$ val and $M \longmapsto N$ for some $N$.
- **Variable preservation:** If $M \longmapsto N$, then the free interval variables in $N$ are a subset of the free variables in $M$.

Given an operational semantics, we define the induced multi-step judgment $M \longmapsto^* N$ and evaluation judgment $M \Downarrow V$ as in **Definition 2.1.1**.

Notably, we do *not* require that the operational semantics is stable under interval substitution. That is, we do not ask that $M$ val implies $M\psi$ val or that $M \longmapsto N$ implies $M\psi \longmapsto N\psi$ for every $\Psi' \Vdash \psi \in \Psi$. Indeed, the operational semantics will contain several rules that fail to be stable in this way. This kind of stability *will* be enforced on the level of typed equality judgments, but not at the level of untyped operational semantics.

On the type system side, the data that defines a type $A$ in an interval context $\Psi$ will now consist of a family of relations indexed by substitutions into $\Psi$, specifying the values of $A\psi$ for each possible $\Psi' \Vdash \psi \in \Psi$.

**Definition 3.1.6 ($\Psi$-relations).** Given $\Psi$ ictx, a $\Psi$-relation $R$ is a family of relations $R\langle\psi\rangle$ indexed by substitutions $\Psi' \Vdash \psi \in \Psi$ from arbitrary interval contexts $\Psi'$ into $\Psi$. A $\Psi$-relation is a $\Psi$-PER when each $R\langle\psi\rangle$ is a PER. Given a $\Psi$-relation $R$ and substitution $\Psi' \Vdash \psi \in \Psi$, we define the $\Psi'$-relation $R\psi$ by $R\psi\langle\psi'\rangle := R\langle\psi\psi'\rangle$.

**Notation 3.1.7.** When $R$ is a $\Psi$-relation and $M$ and $M'$ are terms in context $\Psi$, we will write $M \approx M' \in R$ as syntactic sugar for $M \approx M' \in R\langle\mathrm{id}_\Psi\rangle$. This permits us to write $M \approx M' \in R\psi$ in place of $M \approx M' \in R\langle\psi\rangle$.

Note that we do not require $\Psi$-relations to be stable under substitution in general: we do not ask that $M \approx M' \in R$ implies $M\psi \approx M'\psi \in R\psi$. Indeed, we are primarily interested in $\Psi$-relations on *values*, and it may not even be the case that $V\psi$ is a value for $V$ val.

With each value type assigned a $\Psi$-relation of values, we extend the value relation to terms by *coherent extension*. As described above, we want to require that the interval substitution instances of a term in a type evaluate in a coherent way.