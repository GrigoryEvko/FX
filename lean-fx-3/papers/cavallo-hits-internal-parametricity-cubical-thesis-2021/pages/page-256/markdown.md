244

Cohesive parametric type theory

When the domain is a genuine interval context, we write $\Psi \Vdash \psi = \psi' \in \Upsilon @ m$.

It is simple to check directly that the extended closed substitutions satisfy the properties we eventually hope to extend to all substitutions: the well-formedness of the actions on substitutions and the adjunctions between successive modalities.

Proposition 14.2.13. Given any $\Upsilon' \gg \psi \in \Upsilon @ n$ and $\mu : m \to n$, the action of $\mu$ on $\psi$ is well-typed: we have $\Upsilon'.\mu \gg (\psi : \Upsilon) \otimes \mu \in \Upsilon @ m$.

### Proposition 14.2.14 (Adjunctions).

- We have $\Upsilon'.cc \gg \psi \in \Upsilon @ pt$ if and only if $\Upsilon' \gg \psi \in \Upsilon.dsc @ par$.
- We have $\Upsilon'.dsc \gg \psi \in \Upsilon @ par$ if and only if $\Upsilon' \gg \psi \in \Upsilon.glo @ pt$.

Using the notion of extended substitution, we extend the closed judgments to extended contexts in the standard way: a judgment holds when all of its closed instantiations hold. In turn we get a definition of extended closing substitution.

Definition 14.2.15 (Extended closed judgments). We extend the typing judgments to extended interval contexts pointwise. $\Upsilon \gg A = A'$ pretype @ m is defined to hold when $\Psi \Vdash A\psi = A'\psi$ pretype @ m for all $\Psi \Vdash \psi \in \Upsilon @ m$, and we define $\Upsilon \gg A = A'$ type @ m and $\Upsilon \gg M = M' \in A @ m$ analogously.

Definition 14.2.16 (Extended closing substitutions). We define the extended closing substitutions $\Upsilon \gg \gamma = \gamma' \in \Gamma @ m$ inductively as follows.

$$\frac{\Upsilon \text{ ictx } @ m}{\Upsilon \gg \cdot = \cdot \in \cdot @ m}$$

$$\frac{\Upsilon \gg \gamma = \gamma' \in \Gamma @ n \quad \mu : m \to n \quad \Upsilon.\mu \gg M = M' \in A\gamma @ m}{\Upsilon \gg (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma, (\mu \mid a : A)) @ n}$$

$$\frac{\Upsilon \gg \gamma = \gamma' \in \Gamma @ m \quad \Upsilon \gg r \in \mathbb{I} @ m}{\Upsilon \gg (\gamma, r/x) = (\gamma', r/x) \in (\Gamma, x : \mathbb{I}) @ m} \quad \frac{\Upsilon \gg \gamma = \gamma' \in \Gamma @ m \quad \varepsilon \in \{0, 1\}}{\Upsilon \gg (\gamma, \varepsilon/x) = (\gamma', \varepsilon/x) \in (\Gamma, x : 2) @ m}$$

$$\frac{\Upsilon \setminus r \gg \gamma = \gamma' \in \Gamma @ par \quad \Upsilon \gg r \in \mathbb{I} @ par}{\Upsilon \gg (\gamma, r/x) = (\gamma', r/x) \in (\Gamma, x : \mathbb{I}) @ par}$$

$$\frac{\Upsilon \gg \gamma = \gamma' \in \Gamma @ m \quad \Upsilon \gg \xi\gamma \text{ satisfied } @ m}{\Upsilon \gg \gamma = \gamma' \in (\Gamma, \xi) @ m}$$

We write $\Psi \gg \gamma = \gamma' \in \Gamma @ m$ when the domain is a genuine interval context.