8

SIMON HENRY AND CHRISTOPHER TOWNSEND

any subobject $I \subseteq A$ and for any object $b$ of $\mathcal{C}$, $(\exists_{\alpha}(I))(b) = \exists_{\alpha_b}(I(b))$. (For this last well know fact recall that every object $b$ gives rise to a geometric morphism $p_b : \mathbf{Set} \to \hat{\mathcal{C}}$ whose inverse image is 'evaluate at $b$'; existential quantification $\exists$ commutes with inverse images.)

This example is a standard application of basic topos theory, but it was worth writing out the reasoning in full as it generalises:

**Example 4.2.** Consider the ideal completion of a poset $idl : \mathbf{Pos} \to \mathbf{Pos}$. Then for any poset in $\hat{\mathcal{C}}$, $idl_{\hat{\mathcal{C}}}P \cong \widetilde{idl \circ P}$.

Recall that a subset $I \subseteq P$ is an ideal if and only if various geometric sequents are satisfied ($a \leq b \in I \Rightarrow a \in I, \exists * \in I, a, b \in I \Rightarrow \exists c \in I \land a, b \leq c$). Because these are geometric, they are preserved by any inverse image functor. That is, if $I \subseteq P$ is an ideal in a topos, then for any geometric morphism $f$, $f^*I \subset f^*P$ is again an idea. In particular, if $I \subseteq P$ is an ideal in the topos $\hat{\mathcal{C}}$, then given that evaluation at $a \in \mathcal{C}$ is an inverse image functor, $I(a) \subseteq P(a)$ is an ideal in $\mathbf{Set}$ for each $a \in \mathcal{C}$. In fact, $I \subseteq P$ is an ideal if and only if $I(a) \subseteq P(a)$ is an ideal for each object $a$ of $\mathcal{C}$.

As in the last example $I \subseteq P$ iff for any morphism $f : b \to a$ of $\mathcal{C}$, the image of $I(a)$ under $P(f)$ factors through $I(b)$. But for ideals the image of $I(a)$ under $P(f)$ factors through $I(b)$ iff $idl(P(f))(I(a)) \subseteq I(b)$ (recall for any monotone map $f : P_1 \to P_2$ that $idl(f) : idl(P_1) \to idl(P_2)$ sends an ideal $I$ of $P_1$ to $\downarrow \{f(i) | i \in I\}$). It follows that $idl_{\hat{\mathcal{C}}}P$ is isomorphic to

$$\{(I_a) \in \prod_{a \in Ob(\mathcal{C})} idl(P(a)) | idl(P(f)) I_a \subseteq I_b \ \forall f : b \to a \in \mathcal{C}\}$$

from which we establish $idl_{\hat{\mathcal{C}}}P \cong \widetilde{idl \circ P}$, naturally in $P$, just as in the previous example.

This technique can be applied for any construction that is defined via sets of subsets determined by geometric sequents (provided that the images of the subsets under a presheaf evaluated at a morphism $f : b \to a$ factor iff the constructed morphism (e.g. the $idl(P(f))$ in the last example) evaluated at the domain subset is contain in the codomain subset). In particular:

**Example 4.3.** Consider the completion operation $C : \mathbf{NDL} \to \mathbf{NDL}$ introduced in Proposition 2.3. Then for any normal distributive lattice $N$ in $\hat{\mathcal{C}}$, we have $C_{\hat{\mathcal{C}}}N \cong \widetilde{C \circ N}$.

Indeed, for $N \in \hat{\mathcal{C}}$ an element of $C(N)$ is a subobject of $I \subseteq N$ which satisfies certain geometric axioms, for example "$i \in I$ and $j \leqslant i \Rightarrow j \in I$" or "$a \in I \Rightarrow \exists b \in I, a \triangleleft b$" which can be rewritten as "$a \in I \Rightarrow \exists b \in I, c \in N, a \land c = 0$ and $c \lor b = 1$".

Exactly as in Example 4.2, a subobject of $N$ is a collection of subsets $I(a) \subseteq N(a)$ for each $a \in \mathcal{C}$, such that for $f : b \to a$ in $\mathcal{C}$, the induced map $N(a) \to N(b)$ sends $I(a)$ to $I(b)$. This occurs if and only if $\downarrow \exists_f(I(a)) \subseteq I(b)$. Further, each geometric axiom is satisfied in $\mathcal{C}$ exactly when when it is satisfied by $I(a)$ in $N(a)$, for every $a \in \mathcal{C}$. This provides the identification $C_{\hat{\mathcal{C}}}N \cong \widetilde{C \circ N}$, which is the explicit description needed for the main result.

# 5. PROOF OF THE MAIN THEOREM

We are now ready to prove the main theorem of the paper.