Interpreting specifications 127

(1) By coherent value introduction. For any $\Psi' \Vdash \psi \in \Psi$, we are in one of three cases. If there is some minimal $k$ such that $\xi_i \psi$ is satisfied, then we apply (3) on either side of the equation $N_i \psi \approx N_i' \psi \in \bigoplus R \gamma \psi$, which holds by assumption. If there is no such $k$ but we have $r \psi = s \psi$, then we do the same with (2) and $M \psi \approx M' \psi \in \bigoplus R \gamma \psi$. If we are in neither of these situations, then both terms are values and we have $\text{fhcom}^{r \to s}(M; \xi_i \hookrightarrow x.N_i) \psi \approx \text{fhcom}^{r \to s}(M'; \xi_i \hookrightarrow x.N_i') \psi \in \text{Fhcom}(R) \gamma \psi$ by definition of $\text{Fhcom}(R)$. $\square$

The situation for constructor introduction is a bit more complicated: the coherence of an introduction term depends on the well-behavedness of argument term interpretation, which is used to define the boundary of the constructor in the operational semantics. Conversely, the well-behavedness of argument term interpretation depends on the well-behavedness of prior constructors. We therefore proceed by a mutually inductive argument.

**Definition 6.2.16.** Given a specification $\mathcal{K}$ and a label $\ell \in \mathcal{K}$, write $|\ell|_{\mathcal{K}}$ for the *height of $\ell$ in $\mathcal{K}$*, the index at which $\ell$ occurs in the list $\mathcal{K}$. Given $\mathcal{K}$ and an argument term $M$, define $|M|_{\mathcal{K}}$, the *height of $M$ in $\mathcal{K}$*, to be the maximum height in $\mathcal{K}$ among labels occurring in $M$. We likewise define $|A|_{\mathcal{K}}$ and $|\Theta|_{\mathcal{K}}$ for types and contexts.

**Definition 6.2.17.** Let $\Psi \Vdash \Delta \blacktriangleright \mathcal{K} = \mathcal{K}'$ spec, a $(\Psi, \Delta)$-relation $R$, and $n \in \mathbb{N}$ be given. We say that $R$ *interprets* $\mathcal{K}, \mathcal{K}'$ *below* $n$ when the following two conditions hold for any $\Psi' \Vdash \psi \in \Psi$.

- Given

- $\Psi' \Vdash \Delta \psi \mid \mathcal{K} \psi \mid \Theta \blacktriangleright A = A'$ atype with $|\Theta|_{\mathcal{K} \psi}, |A|_{\mathcal{K} \psi}, |A'|_{\mathcal{K} \psi}$ all less than $n$,
- $\chi \approx \chi' \in \{\Theta\}_{\mathcal{K} \psi}(R \psi)$,

we have $\{\Theta.A\}_{\mathcal{K} \psi}(R \psi, \chi) = \{\Theta.A'\}_{\mathcal{K} \psi}(R \psi, \chi')$.

- Given

- $\Psi' \Vdash \Delta \psi \mid \mathcal{K} \psi \mid \Theta \blacktriangleright M = M' \in A$ with $|\Theta|_{\mathcal{K} \psi}, |M|_{\mathcal{K} \psi}, |M'|_{\mathcal{K} \psi}, |A|_{\mathcal{K} \psi}$ all less than $n$,
- $\chi \approx \chi' \in \{\Theta\}_{\mathcal{K} \psi}(R \psi)$,

we have $(\Theta.M)_{\mathcal{K} \psi}(\chi) \approx (\Theta.M')_{\mathcal{K}' \psi}(\chi') \in \bigoplus \{\Theta.A\}_{\mathcal{K} \psi}(R \psi, \chi)$.

Note that these operations are always *well-defined*; the condition is that they preserve equality in their inputs (and in the latter case, are in the field of a relation). Note that when these conditions hold, it follows by induction that the interpretation functions for contexts and substitutions of height below $n$ are likewise well-behaved.