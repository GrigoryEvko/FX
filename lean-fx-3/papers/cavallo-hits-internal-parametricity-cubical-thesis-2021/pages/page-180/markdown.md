168 Parametric cubical type theory

## 9.1 The bridge interval

The first step is to extend the theory of interval contexts and substitutions from Section 3.1.1 with the new bridge interval, which exists in parallel with the cubical path interval. For the most part, we will not repeat the cubical elements here; instead we present only the new components, which are typically either definitions of new judgments or extensions of existing inductively defined judgments by new rules.

### 9.1.1 Interval contexts and substitutions

**Definition 9.1.1 (Interval contexts).** We extend the interval context judgment $\Psi$ ictx, specified in Definition 3.1.2, by adding extension by a bridge interval as a context former.

$$\frac{\Psi \text{ ictx}}{(\Gamma, x : \mathbf{I}) \text{ ictx}}$$

**Definition 9.1.2 (Bridge interval elements).** $\Psi \Vdash r \in \mathbf{I}$ holds when $r = 0$, $r = 1$, or $r = x$ for some $(x : \mathbf{I}) \in \Psi$.

We see our first difference between the two intervals in the definition of substitution. Recall that we define substitutions into a context with a path interval hypothesis as shown below.

$$\frac{\Psi' \Vdash \psi \in \Psi \qquad \Psi' \Vdash r \in \mathbb{I}}{\Psi' \Vdash (\psi, r/x) \in (\Psi, x : \mathbb{I})}$$

As described above, we intend the bridge interval to be affine, so we cannot define substitutions into contexts with a bridge hypothesis in the same way; it is easy to construct a contraction substitution from this rule. Intuitively, a substitution $\Psi' \Vdash \psi \in (\Psi, x : \mathbf{I})$ should still consist of two components: a substitution $\Psi' \Vdash \psi' \in \Psi$ and a bridge term $\Psi' \Vdash r \in \mathbf{I}$. In this case, however, we want to also ensure that the same variable is not used twice between $\psi'$ and $r$: in other words, if $r$ is a variable in $\Psi'$, then $\psi'$ should not use that variable.

To express this condition, we define an *interval restriction* operation that removes an interval variable from its context. Here we adapt the nominal restriction operation from Cheney's *nominal type theory* [Che12], which likewise extends type theory with a new kind of affine hypothesis; we only adjust the definition to accommodate the constants 0 and 1. Restriction by these has no effect: while we cannot duplicate variables, we can use constants freely.