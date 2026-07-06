1.2. GRAY OPERATIONS

Lemma 1.2.5.10. Let A, B, C, D, and E be presheaves on Θ, and k, m, n be integers. There exists a natural morphism

$$(\_)_A : \operatorname{Hom}([B, m], C \otimes [D, n]) \to \operatorname{Hom}([A \otimes B, m], C \otimes [A \otimes D, n])$$

such that for any pair of morphisms $f : [B, m] \to C \otimes [n]$ and $g : [F, k] \to E \otimes [m]$,

$$\mathbf{F}(((E \otimes f) \circ g_B)_A) = \mathbf{F}((E \otimes f_A) \circ (g_B)_A)$$

Proof. It is sufficient to describe this morphism when $A, B, C, D$, and $E$ are representable. This allows us the use of Steiner theory to construct this application. Let $f : [B, m] \to C \otimes [D, n]$ be a morphism. We set $f_A : [A \otimes B, m] \to C \otimes [A \otimes D, n]$ as the unique morphism of $(0, \omega)$-categories such that for every $a \in B_A$, $b \in B_B$, and $m \in B_m$

$$\lambda f_A([a \otimes b, m]) := \sum_{i \le n} c_i \otimes [a \otimes d_i, n_i]$$

where $(c_i, d_i, n_i)$ is the unique sequence of elements of $B_C \times B_D \times B_{[n]}$ such that $\lambda f([b, m]) = \sum_{i \le n} c_i \otimes [d_i, n_i]$. The equality $\lambda f_A \partial = \partial \lambda f_A$ and the equality $\mathbf{F}(((E \otimes f) \circ g_B)_A) = \mathbf{F}((E \otimes f_A) \circ (g_B)_A)$ is a straightforward calculation using Steiner theory.

Lemma 1.2.5.11. Let A, B, C, D, E, and F be presheaves on Δ, and k, m, n, l be integers. There exists a natural morphism

$$\alpha : \operatorname{Hom}([A, k], B \otimes [m]) \times \operatorname{Hom}([C, m], D \otimes [n]) \to \operatorname{Hom}([C \times A, k], (B \times D) \otimes [n])$$

and such that for any $f : [A, k] \to B \otimes [m]$, $g : [C, m] \to D \otimes [n]$, and $h : [E, n] \to F \otimes [l]$,

$$\alpha(\alpha(f, g), h) = \alpha(f, \alpha(g, h)) \tag{1.2.5.12}$$

Proof. Let $f : [A, k] \to B \otimes [m]$ and $g : [C, m] \to D \otimes [n]$ be two morphisms. Using the application of lemma 1.2.5.10 and the canonical morphism of 1.2.5.9, we get a sequence of arrows

$$[C \otimes A, k] \xrightarrow{f_C} B \otimes [C, m] \xrightarrow{B \otimes g} B \otimes (D \otimes [n]) \longrightarrow (B \times D) \otimes [n]$$

whose composite is denoted $\alpha'(f, g)$. Remark now that $(B \times D) \otimes [n]$ is a Θ₂-set. Moreover, we have an isomorphism

$$\tau_2^i([C \otimes A, k]) \cong [\tau_1^i(C \otimes A), k] \cong [C \times A, k]$$

We then set

$$\alpha(f, g) := \tau_2^i(\alpha'(f, g)) := [C \times A, k] \to (B \times D) \otimes [n].$$

Now, suppose given two arrows $f : [A, k] \to B \otimes [m]$, $g : [C, m] \to D \otimes [n]$, and $h : [E, n] \to F \otimes [l]$. Unfolding the definition, we have that $\alpha(\alpha(f, g), h)$ and $\alpha(f, \alpha(g, h))$ are respectively the image by $\tau_2^i$ of the morphism

$$[E \otimes (C \otimes A), k] \xrightarrow{(B \otimes g_E) \circ (f_C)_E} B \otimes (D \otimes [E, n]) \xrightarrow{B \otimes (D \otimes h)} B \otimes (D \otimes (F \otimes [k])) \longrightarrow (B \times D \times F) \otimes [l]$$

and

$$[E \otimes (C \otimes A), k] \xrightarrow{(B \otimes g \circ (f_C)_E)} B \otimes (D \otimes [E, n]) \xrightarrow{B \otimes (D \otimes h)} B \otimes (D \otimes (F \otimes [k])) \longrightarrow (B \times D \times F) \otimes [l]$$

55