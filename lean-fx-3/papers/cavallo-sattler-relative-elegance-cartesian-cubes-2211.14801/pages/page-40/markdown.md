40

E. Cavallo and C. Sattler

of sets is an isomorphism.

Informally, the weight $W$ specifies how many "copies" of each object in the diagram $F$ to include in the weighted colimit $W \circledast_{\mathbf{C}} F$.

Example 5.2 The ordinary colimit of a diagram $F: \mathbf{C} \to \mathbf{E}$ can be described as $1 \circledast_{\mathbf{C}} F$, a colimit weighted by the terminal presheaf $1 \in \mathrm{PSh}(\mathbf{C})$. Conversely, any weighted colimit $W \circledast_{\mathbf{C}} F$ admits a characterization as an ordinary colimit over the category of elements of $W$:

$$W \circledast_{\mathbf{C}} F \cong \operatorname{colim}\left(\operatorname{el} W \xrightarrow{\pi} \mathbf{C} \xrightarrow{F} \mathbf{E}\right).$$

In particular, any cocomplete category has weighted colimits.

Example 5.3 Recall that a tensor of a set $S \in \mathbf{Set}$ and object $X \in \mathbf{E}$ is an object $S * X$ such that morphisms $S * X \to Y$ correspond to objects $\mathbf{Set}(S, \mathbf{E}(X, Y))$, i.e., families of morphisms $f_s: X \to Y$ for $s \in S$. In ordinary category theory, this is simply the $S$-ary coproduct $\coprod_{s \in S} X$, so can be expressed as the weighted colimit $1 \circledast_S \Delta X$ of the constant diagram $\Delta X: S \to \mathbf{E}$. Alternatively, we can encode the tensor as the $S$-weighted colimit $S \circledast_1 X$ of the diagram $X: \mathbf{1} \to \mathbf{E}$ over the terminal category. We can characterize any weighted colimit $W \circledast_{\mathbf{C}} F$ as a coend of tensors:

$$W \circledast_{\mathbf{C}} F \cong \int^{c \in \mathbf{C}} W_c * F^c.$$

We will always be working in cocomplete categories. For a given $\mathbf{C}$, weighted colimits over $\mathbf{C}$ are then functorial in both the weight and the diagram, giving a bifunctor $\circledast_{\mathbf{C}}: [\mathbf{C}^{\mathrm{op}}, \mathbf{Set}] \times [\mathbf{C}, \mathbf{E}] \to \mathbf{E}$. This functoriality will be an essential tool. In particular, we will often take a family of weighted colimits over a family of weights:

Notation 5.4 Given a family of weights $W: \mathbf{D} \times \mathbf{C}^{\mathrm{op}} \to \mathbf{Set}$ and $F: \mathbf{C} \to \mathbf{E}$, we write $W \circledast_{\mathbf{C}} F: \mathbf{D} \to \mathbf{E}$ for the result of calculating the weighted colimit pointwise, that is $(W \circledast_{\mathbf{C}} F)^d := W^d \circledast_{\mathbf{C}} F$.

Remark 5.5 From the characterization in terms of ordinary colimits, it follows that weighted colimits in presheaf categories are computed pointwise. Thus for $W: \mathbf{C}^{\mathrm{op}} \to \mathbf{Set}$ and $F: \mathbf{C} \times \mathbf{D}^{\mathrm{op}} \to \mathbf{Set}$, we have $(W \circledast_{\mathbf{C}} F)_d \cong W \circledast_{\mathbf{C}} F_d$, where on the left we regard $F$ as a functor $\mathbf{C} \to \mathrm{PSh}(\mathbf{D})$.

It follows quickly from the universal property defining weighted colimits that the bifunctor $\circledast_{\mathbf{C}}$ preserves colimits in both arguments. It is therefore determined by its behavior on representable weights, which is simply characterized:

Proposition 5.6 Naturally in $c \in \mathbf{C}$ and $X: \mathbf{C} \to \mathbf{E}$, we have $\not\cong c \circledast_{\mathbf{C}} X \cong X^c$. ■

Corollary 5.7 Naturally in $W: \mathbf{D}^{\mathrm{op}} \to \mathbf{Set}$, $V: \mathbf{D} \times \mathbf{C}^{\mathrm{op}} \to \mathbf{Set}$, and $F: \mathbf{C} \to \mathbf{E}$, we have $(W \circledast_{\mathbf{D}} V) \circledast_{\mathbf{C}} F \cong W \circledast_{\mathbf{D}} (V \circledast_{\mathbf{C}} F)$.

2025/10/16 00:43