Vol. 17:4

INTERNAL PARAMETRICITY FOR CUBICAL TYPE THEORY

5:37

get the same result up to the equality defined by $\tau^{\Downarrow}$.

$$\begin{array}{c c c} A \psi_1 & \Longrightarrow & A_1 \\ -\psi_2 \downarrow & & \downarrow -\psi_2 \\ A \psi_1 \psi_2 & \tau^{\Downarrow} & A_1 \psi_2 \end{array}$$

Note that the candidate judgments are stable under interval substitution by definition: for example, if $\Psi \Vdash M \sim M' \in \alpha$, then $\Psi' \Vdash M\psi \sim M'\psi \in \alpha\psi$ for any $\Psi' \Vdash \psi \in \Psi$.

A candidate is a value type system when the typing relation satisfies several additional conditions, which require that each type names at most one relation, that the type and element relations are partial equivalence relations, and that any value type is *coherently* a type.

**Definition 4.7.** A *value type system* $\tau$ is a candidate value type system satisfying the following.

**Unicity:** If $\tau(\Psi, V, V', \varphi)$ and $\tau(\Psi, V, V', \varphi')$, then $\varphi = \varphi'$.

**PER:** $\tau(\Psi, -, -, \varphi)$ is a partial equivalence relation (PER) for all $\Psi, \varphi$.

**PER-valuation:** If $\tau(\Psi, V, V', \varphi)$, then $\varphi$ is a PER.

**Value-coherence:** If $\tau(\Psi, V, V', \varphi)$, then $\Psi \Vdash V \sim V' \downarrow \alpha \in \tau$ for some $\alpha$.

Likewise, we will require that the values related by the relations associated to types are in fact coherently related.

**Definition 4.8.** We say a $\Psi$-relation $\alpha$ is *value-coherent* and write $\operatorname{Coh}(\alpha)$ if $\alpha_{\psi}(V, V')$ implies $\Psi' \Vdash V\psi \sim V'\psi \in \alpha\psi$ for all $\psi$ and $V, V'$.

Given a value type system, we obtain typing judgments first on closed and then on open terms. For types, we also distinguish between *pretypes* and *types*, the latter of which are required to support Kan operations. For the following series of definitions, we fix an ambient value type system $\tau$.

**Definition 4.9.** We define the closed judgments as follows.

- $\triangleright \Psi \Vdash A = A'$ pretype holds when $\Psi \Vdash A \sim A' \downarrow \alpha \in \tau$ for some value-coherent $\alpha$.
- $\triangleright$ Presupposing $\Psi \Vdash A = A$ pretype, $\Psi \Vdash M = M' \in A$ holds when $\Psi \Vdash A \sim A \downarrow \alpha \in \tau$ with $\Psi \Vdash M \sim M' \in \alpha$.

We define $\Psi \Vdash A$ pretype to mean $\Psi \Vdash A = A$ pretype, likewise $\Psi \Vdash M \in A$ to mean $\Psi \Vdash M = M \in A$. We will abbreviate future reflexive judgments in this fashion without comment. When we have $\Psi \Vdash A$ pretype, we write $[[A]]$ for the (necessarily unique) value $\Psi$-relation assigned to $A$ by the value type system.

We now extend the closed judgments to *open judgments*, defined on terms containing arbitrary variables. We do so by means of a *context instantiation judgment* $\Psi \Vdash \gamma = \gamma' \in \Gamma$, which specifies the ways a general context $\Gamma$ may be instantiated by closed terms over $\Psi$.

**Definition 4.10.** We define the context instantiations $\Psi \Vdash \gamma = \gamma' \in \Gamma$ inductively as follows.

- $\triangleright \Psi \Vdash \cdot = \cdot \in \cdot$.
- $\triangleright \Psi \Vdash (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma, a : A)$ when $\Psi \Vdash \gamma = \gamma' \in \Gamma$ and $\Psi \Vdash M = M' \in A\gamma$.
- $\triangleright \Psi \Vdash (\gamma, r/x) = (\gamma, r/x) \in (\Gamma, x : \mathbb{I})$ when $\Psi \Vdash \gamma = \gamma' \in \Gamma$ and $\Psi \Vdash r \in \mathbb{I}$.
- $\triangleright \Psi \Vdash (\gamma, \boldsymbol{r}/\boldsymbol{x}) = (\gamma, \boldsymbol{r}/\boldsymbol{x}) \in (\Gamma, \boldsymbol{x} : \mathbb{I})$ when $\Psi \Vdash \boldsymbol{r} \in \mathbb{I}$ and $\Psi \setminus \boldsymbol{r} \Vdash \gamma = \gamma' \in \Gamma$.