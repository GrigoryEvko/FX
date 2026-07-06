52

Cubical type theory

$M \Downarrow V$. On the other hand, we can substitute 0 for $x$ to obtain $M[0/x] \in A[0/x]$ and then evaluate: $M[0/x] \Downarrow V_0$. What should the relationship between $V[0/x]$ and $V_0$ be?

If we assume that the typing judgments are stable under substitution and that terms are equal to their values—which we would certainly like to be true—then we will have that $x : \mathbb{I} \gg M = V \in A$, thus $M[0/x] = V[0/x] \in A[0/x]$, as well as $M[0/x] = V_0 \in A[0/x]$. It follows that $V[0/x] = V_0 \in A[0/x]$. Flipping our perspective around, if we want stability under substitution and equality to values, we must ensure that our definition of the term judgment guarantees these kind of coherence equations. It is too permissive to say that $x : \mathbb{I} \gg M \in A$ whenever $M$ evaluates to a value in $A$; we must require that all the substitution instances of $M$ evaluate in a coherent way. The two ideas of *evaluation in an interval context* and *coherent evaluation* form the basis of the computational interpretation of cartesian cubical type theory as presented by Angiuli, Favonia, and Harper, as well as the proof of canonicity for De Morgan cubical type theory due to Huber.

### 3.1.1 Interval contexts

Now getting into the definition of the framework proper, we first want to distinguish the contexts and substitutions that deal only with interval assumptions; the contexts in which we consider terms to be “closed”. We use the letters $\Psi$ and $\psi$ for these contexts and substitutions, distinguishing them from the general $\Gamma$ and $\gamma$. The interval judgments are prior to the definitions that deal with terms; in particular, they do not depend at all on the choice of type system.

**Definition 3.1.2 (Contexts).** The well-formed interval contexts, $\Psi$ ictx, are inductively defined by the following rules.

$$\overline{\cdot \text{ictx}} \qquad \frac{\Psi \text{ ictx}}{(\Psi, x : \mathbb{I}) \text{ ictx}}$$

**Definition 3.1.3 (Interval elements).** $\Psi \Vdash r \in \mathbb{I}$ holds when $r = 0$, $r = 1$, or $r = x$ for some $(x : \mathbb{I}) \in \Psi$.

**Definition 3.1.4 (Interval substitutions).** The well-formed interval substitutions, $\Psi' \Vdash \psi \in \Psi$, are inductively defined by the following rules.

$$\overline{\Psi' \Vdash \cdot \in \cdot} \qquad \frac{\Psi' \Vdash \psi \in \Psi \qquad \Psi' \Vdash r \in \mathbb{I}}{\Psi' \Vdash (\psi, r/x) \in (\Psi, x : \mathbb{I})}$$