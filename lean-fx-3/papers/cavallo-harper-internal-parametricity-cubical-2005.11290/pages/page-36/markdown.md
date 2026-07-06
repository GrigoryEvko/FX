5:36

E. CAVALLO AND R. HARPER

Vol. 17:4

useful to first introduce candidate value type systems and then impose additional conditions under which a candidate is an actual type system.

Definition 4.3. A candidate value type system $\tau$ is a quaternary relation $\tau(\Psi, V, V', \varphi)$ ranging over contexts $\Psi$, values $V, V'$ in context $\Psi$, and binary relations $\varphi$ on values in context $\Psi$.

We read an instance $\tau(\Psi, V, V', \varphi)$ of the relation as specifying that (1) the values $V$ and $V'$ are equal types in context $\Psi$ and that (2) these type names stand for the relation $\varphi$: values $W$ and $W'$ are equal elements of $V$ (likewise $V'$) in context $\Psi$ when $\varphi(W, W')$ holds.

Given a candidate value type system, we derive candidate judgments extending the defining relations to non-value terms. In [All87], a term is a type (resp. well-typed) when it evaluates to a type value (resp. well-typed value). In a setting with interval variables, it becomes necessary to require a stronger “coherent evaluation” condition: to be well-typed, a term must not merely evaluate to a well-typed value, but do so in a way that interacts in a sensible way with interval substitutions. First, we define “incoherent” extensions of value type systems and terms to terms.

Definition 4.4. Given a candidate value type system, we write $\tau^{\Downarrow}(\Psi, A, A', \varphi)$ for (possibly non-value) terms $A, A'$ to mean that $A \Downarrow V$ and $A' \Downarrow V'$ for some $V, V'$ with $\tau(\Psi, V, V', \varphi)$. Given a relation $\varphi$ on values, we define a relation $\varphi^{\Downarrow}$ on terms: $\varphi^{\Downarrow}(M, M')$ holds when $M \Downarrow V$ and $M' \Downarrow V'$ for some $V, V'$ with $\varphi(V, V')$.

To cut down to the coherently well-behaved types and terms, we introduce a notion of $\Psi$-relation, a family of relations indexed by the substitutions into $\Psi$.

Definition 4.5. A $\Psi$-relation $\alpha$ is a family of binary relations $\alpha_{\psi}$, indexed by substitutions $\Psi' \Vdash \psi \in \Psi$ into $\Psi$ and where each $\alpha_{\psi}$ relates terms in context $\Psi'$. Given a $\Psi$-relation $\alpha$ and $\Psi' \Vdash \psi \in \Psi$, we define a $\Psi'$-relation $\alpha\psi$ by $(\alpha\psi)_{\psi'} := \alpha_{\psi\psi'}$.

We now define the coherent candidate judgments: $\Psi \Vdash A \sim A' \downarrow \alpha \in \tau$, which asserts that $A$ and $A'$ coherently evaluate to equal type names standing for the $\Psi$-relation $\alpha$, and $\Psi \Vdash M \sim M' \in \alpha$, which asserts that $M$ and $M'$ coherently evaluate to values equal in $\alpha$.

Definition 4.6. We define the candidate judgments as follows.

$\triangleright \Psi \Vdash A \sim A' \downarrow \alpha \in \tau$ holds when for every $\Psi_1 \Vdash \psi_1 \in \Psi$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$, we have

- (1) $A\psi_1 \Downarrow A_1$ and $A'\psi_1 \Downarrow A_1'$ for some $A_1, A_1'$,
- (2) there is some $\varphi$ such that $\tau^{\Downarrow}(\Psi_2, -, -, \varphi)$ relates $(A_1\psi_2, A\psi_1\psi_2)$ and its reverse, $(A_1'\psi_2, A'\psi_1\psi_2)$ and its reverse, and $(A_1\psi_2, A_1'\psi_2)$,

and $\alpha$ is a $\Psi$-relation on values such that $\tau^{\Downarrow}(\Psi', A\psi, A'\psi, \alpha_{\psi})$ for all $\Psi' \Vdash \psi \in \Psi$.

$\triangleright \Psi \Vdash M \sim M' \in \alpha$ holds when for every $\Psi_1 \Vdash \psi_1 \in \Psi$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$, we have

- (1) $M\psi_1 \Downarrow M_1$ and $M'\psi_1 \Downarrow M_1'$ for some $M_1, M_1'$,
- (2) $(\alpha_{\psi_1\psi_2})^{\Downarrow}$ relates $(M_1\psi_2, M\psi_1\psi_2)$ and its reverse, and $(M_1'\psi_2, M_1'\psi_2)$.

The conditions in the definition of $\Psi \Vdash A \sim A' \downarrow \alpha \in \tau$, for example, ask that we have the square shown below: whether we apply $\psi_2$ to $A\psi_1$ or first evaluate and then apply $\psi_2$, we