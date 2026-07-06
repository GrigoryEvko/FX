A logic of programs 25

*Proof.* We give the proof for type symmetry; the others follow the same pattern. Suppose that $\Gamma \gg A = B$ type. To show $\Gamma \gg B = A$ type, let an arbitrary $\Vdash \gamma = \gamma' \in \Gamma$; we must show that $\Vdash B\gamma = A\gamma'$ type. By symmetry of the closing substitution judgment, we have $\Vdash \gamma' = \gamma \in \Gamma$. Applying $\Gamma \gg A = B$ type with this substitution, we get $\Vdash A\gamma' = B\gamma$ type. By symmetry of the closed typing judgment, we thus conclude $\Vdash B\gamma = A\gamma'$ type. $\square$

Rules for open judgments follow in general from the closed case in this fashion: each instance of the hypotheses implies the corresponding instance of the conclusion. For this reason, we will typically only give proofs for closed versions of rules.

**Exact coercion** Unicity of the value type system implies the important *exact coercion* rule, which allows us to transfer terms between equal types.

# **Rule 2.1.16 (Exact coercion).**

$$\frac{\Gamma \gg M = M' \in A \quad \Gamma \gg A = B \text{ type}}{\Gamma \gg M = M' \in B}$$

**Structural rules** The *structural rules* describe the behavior of variables in the context. *Weakening* states that any true judgment is still true in the presence of additional hypotheses; *cut* allows us to substitute terms for variables. For types, for example, we have the following; similar principles apply to their elements.

# **Rules 2.1.17 (Structural rules for types).**

$$\frac{\text{WEAKENING}}{\Gamma \gg A = A' \text{ type} \quad \Gamma \gg B \text{ type}} \quad \frac{\text{CUT}}{\Gamma, b : B \gg A = A' \text{ type} \quad \Gamma \gg N = N' \in B} \quad \frac{\Gamma, b : B \gg A = A' \text{ type} \quad \Gamma \gg N = N' \in B}{\Gamma \gg A[N/b] = A'[N'/b] \text{ type}}$$

**Open substitutions** Although not strictly necessary to fill out the picture in Figure 2.1, it is useful to introduce a notion of *open* substitutions, substitutions from one context to another. We can define these in the same way we defined closed substitutions, just with all judgments parameterized by another context.

**Definition 2.1.18 (Open substitutions).** We define $\Gamma' \gg \gamma = \gamma' \in \Gamma$ to be the least judgment closed under the following principles.

$$\frac{\Gamma' \gg \gamma = \gamma' \in \Gamma \quad \Gamma' \gg M = M' \in A\gamma}{\Gamma' \gg (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma, a : A)}$$