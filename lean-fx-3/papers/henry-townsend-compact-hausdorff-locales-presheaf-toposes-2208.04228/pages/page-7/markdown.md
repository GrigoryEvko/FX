COMPACT HAUSDORFF LOCALES IN PRESHEAF TOPOSES

7

Example 4.1. Recall the powerset construction, $P : \mathbf{Set} \to \mathbf{Pos}$, which sends a set to its powerset and $f : A \to B$ to $\exists_f : PA \to PB$. This can be done in any topos; given an object $A$ of $[\mathcal{C}^{op}, \mathbf{Set}]$, i.e. a presheaf, consider its powerset $P_{\mathcal{C}}A : \mathcal{C}^{op} \to \mathbf{Pos}$. In this example we show that $P_{\mathcal{C}}A \cong \widetilde{P \circ A}$.

We will first assume that $\mathcal{C}$ has a terminal object 1 and show that $P_{\mathcal{C}}A$ evaluated at 1 is isomorphic to $\widetilde{P \circ A}$ evaluated at 1. The presheaf $P_{\mathcal{C}}A$ evaluated at 1 is $Sub_{\mathcal{C}}(A)$, i.e. the collection of monomorphisms from $I$ to $A$. But a subobject $I \subseteq A$ is a collection of subobjects $I(a) \subseteq A(a)$ such that for any morphism $f : b \to a$ of $\mathcal{C}$, the image of $I(a)$ under $A(f)$ factors through $I(b)$. This is just another way of stating that the morphism $I \subseteq A$ is a natural transformation. As the image of $I(a)$ under $P(f)$ factors through $I(b)$ iff $\exists_{A(f)}(I(a)) \subseteq I(b)$, it follows that $P_{\mathcal{C}}A$ is isomorphic to

$$\{(I_a) \in \prod_{a \in Ob(\mathcal{C})} P(A(a)) | \exists_{A(f)} I_a \subseteq I_b \ \forall f : b \to a \in \mathcal{C}\}.$$

Given a general object $a$ of $\mathcal{C}$, recall that $[\mathcal{C}^{op}, \mathbf{Set}] / \mathcal{C}(\_a) \simeq [(\mathcal{C}/a)^{op}, \mathbf{Set}]$ so there is a geometric morphism $\gamma_a : \mathcal{C}/a \to \tilde{\mathcal{C}}$ whose inverse image has a left adjoint (it is a slice, A4.1.3 [J02]). The left adjoint sends 1 to $\mathcal{C}(\_a)$ and the inverse image is precomposition with the forgetful functor $\Sigma_a^{op} : (\mathcal{C}/a)^{op} \to \mathcal{C}^{op}$ (A4.1.4). Now $P_{\mathcal{C}}A(a)$ is naturally isomorphic to $Nat[\mathcal{C}(\_a), P_{\mathcal{C}}A]$ which is, via this adjunction, isomorphic to

$$Nat[1, \gamma_a^* P_{\mathcal{C}}A] \cong Nat[1, P_{\mathcal{C}/a}(A \circ \Sigma_a)]$$

where the isomorphism follows as $\gamma_a$ is logical (all geometric morphisms that are slices are logical; e.g. A2.3.2 [J02]) and so its inverse image commutes with the powerset. As $\mathcal{C}/a$ has a terminal object we can apply the above reasoning to conclude that $P_{\mathcal{C}}A(a)$ is isomorphic to

$$\{(I_f) \in \prod_{f:b \to a} P(A(b)) | \exists_{A(g)} I_f \subseteq I_{fg} \ \forall c \xrightarrow{g} b \xrightarrow{f} a\}$$

which is the lax limit of the diagram $(\mathcal{C}/a)^{op} \xrightarrow{\Sigma_a^{op}} \mathcal{C}^{op} \xrightarrow{P \circ A} \mathbf{Pos}$. This establishes order isomorphisms $P_{\mathcal{C}}A(a) \cong \widetilde{P \circ A}(a)$ for every object $a$ of $\mathcal{C}$.

We must also check that these order isomorphisms are natural for any morphism $h : a' \to a$ of $\mathcal{C}$. This essentially follows as $\gamma_{a'} \cong \gamma_h \gamma_a$. The effect of $\gamma_h^*$ on subobjects $I \subseteq A \circ \Sigma_a^{op}$ is precomposition with the 'postcompose with $h$' functor $\Sigma_h^{op} : (\mathcal{C}/a')^{op} \to (\mathcal{C}/a)^{op}$. So $(I_f)_{f:b \to a}$ is mapped to $(I_{hf'})_{f':b' \to a'}$ by $\gamma_h^*$ which is the formula we have given for $\widetilde{P \circ A}(h)$.

Finally we need to check naturality with respect to a natural transformation $\alpha : A \to B$ (i.e. with respect to a morphism of $\tilde{\mathcal{C}}$). That is we must check that

$$\begin{array}{ccc} P_{\mathcal{C}}A & \xrightarrow{\cong} & \widetilde{P \circ A} \\ \downarrow{\exists_\alpha} & & \downarrow{\widetilde{P\alpha}} \\ P_{\mathcal{C}}B & \xrightarrow{\cong} & \widetilde{P \circ B} \end{array}$$

commutes. As above this can be seen by first checking the case of the diagram evaluated at $a = 1$ and then applying change of base. The case $a = 1$ follows as for