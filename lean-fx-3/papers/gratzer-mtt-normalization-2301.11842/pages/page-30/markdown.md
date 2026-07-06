27:30

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

The fact that $\operatorname{Sig}^{*}(A, B).\text{code}$ and $\operatorname{Sig}^{*}(A, B).\text{pred}$ lie over $\operatorname{Sig}(A, B)$ and $\operatorname{Tm}_{m}(z, \operatorname{Sig}(z, A, B))$ follows from their definition and realignment. $\square$

**Lemma 5.9.** $(\mathsf{Ty}_m^*, \mathsf{Tm}_m^*)$ is closed under booleans and the relevant constants lie over their counterparts in $(\mathsf{Ty}_m, \mathsf{Tm}_m)$.

*Proof.* We must implement the following constants:

$$
\begin{array}{l}
\mathsf{Bool}^*: \{\mathsf{Ty}_m^* \mid z: \mathbf{syn} \mapsto \mathsf{Bool}(z)\} \\
\mathsf{true}^*: \{\mathsf{Tm}_m^*(\mathsf{Bool}^*) \mid z: \mathbf{syn} \mapsto \mathsf{true}\} \\
\mathsf{false}^*: \{\mathsf{Tm}_m^*(\mathsf{Bool}^*) \mid z: \mathbf{syn} \mapsto \mathsf{false}\} \\
\mathsf{if}^*: (A: \mathsf{Tm}_m^*(\mathsf{Bool}^*) \to \mathsf{Ty}_m^*) \\
\quad \to \mathsf{Tm}_m^*(A(\mathsf{true}^*)) \\
\quad \to \mathsf{Tm}_m^*(A(\mathsf{false}^*)) \\
\quad \to (b: \mathsf{Tm}_m^*(\mathsf{Bool}^*)) \\
\quad \to \{\mathsf{Tm}_m^*(A(b)) \mid z: \mathbf{syn} \mapsto \mathsf{if}(A, t, f, b)\} \\
\quad : (A: \mathsf{Tm}_m^*(\mathsf{Bool}^*) \to \mathsf{Ty}_m^*) \\
\quad \to (t: \mathsf{Tm}_m^*(A(\mathsf{true}^*))) \\
\quad \to (f: \mathsf{Tm}_m^*(A(\mathsf{false}^*))) \\
\quad \to (\mathsf{if}^*(A, t, f, \mathsf{true}^*) = t) \times (\mathsf{if}^*(A, t, f, \mathsf{false}^*) = f)
\end{array}
$$

First, we define $\Phi$ by realignment:

$$
\begin{array}{l}
\text{record } \Phi: \{\mathsf{U}_1 \mid z: \mathbf{syn} \mapsto \mathsf{Tm}_m(z, \mathsf{Bool})\} \text{ where} \\
\quad \mathsf{tm}: \mathsf{Nf}_m(\mathsf{Bool}) \\
\quad \mathsf{prf}: \bullet \left( \begin{array}{l} \sum_{e: \mathsf{Ne}_m(\mathsf{Bool})} \mathsf{tm} = \mathbf{up}(e) \\ + \sum_{b: \mathbf{2}} \mathsf{tm} = \mathsf{rec}_2(b; \mathsf{tt}; \mathsf{ff}) \end{array} \right)
\end{array}
$$

In the above, we have used $\mathsf{rec}_2$ for the ordinary elimination principle for $\mathbf{2}$ in $\mathcal{G}$. We have opted for the names $\mathbf{2}$ and $\mathsf{rec}_2$ in the hopes of avoiding ambiguity with $\mathsf{Bool}$, $\mathsf{if}$, and $\mathsf{if}$.

We may now define $\mathsf{Bool}^*$:

$$
\begin{array}{l}
\mathsf{Bool}^*.\text{code} = \mathbf{Bool} \\
\mathsf{Bool}^*.\text{pred} = \Phi \\
\mathsf{Bool}^*.\text{reflect} = \lambda e. \langle \mathbf{up}(e), \eta(\iota_1(e, \star)) \rangle \\
\mathsf{Bool}^*.\text{reify} = \lambda b. b.\mathsf{tm}
\end{array}
$$

It remains to define the introduction and elimination forms.

$$
\begin{array}{l}
\mathsf{true}^* = \langle \mathbf{tt}, \eta(\iota_2(0, \star)) \rangle \\
\mathsf{false}^* = \langle \mathbf{ff}, \eta(\iota_2(1, \star)) \rangle
\end{array}
$$

The elimination form is defined by constructing a map out of $\bullet X$, by taking advantage of its definition as a pushout (Diagram 4.1):

$$
\mathsf{if}^*(A, t_0, t_1, b = \langle \mathsf{tm}, \mathsf{prf} \rangle) =
$$