Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:29

Definition 4.16. Let $\Phi$ be a finite list of abstract objects and let $K$ be an additional abstract object, such that $K$ and each object of $\Phi$ is either linear or nonlinear and has a chosen sign. Let $\mathcal{C}art_{\Phi/K}$ be the LNL polycategory whose objects are those of $\Phi$ and $K$ and having precisely one nonidentity morphism $f \in \mathcal{C}art_{\Phi/K}(\Phi, K)$. This is an abstract cone with vertex $K$; we call it the **abstract cartesianness cone** determined by $\Phi$ and $K$.

Observe that a concrete cone $G : \mathcal{C}art_{\Phi/K} \to \mathcal{P}$ is determined by a single morphism $Gf \in \mathcal{P}(G\Phi, GK)$.

Proposition 4.17. For any $\phi : \mathcal{P} \to \mathcal{Q}$, a concrete cone $G : \mathcal{C}art_{\Phi/K} \to \mathcal{P}$ is $\pi$-extremal if and only if $Gf$ is $\pi$-cartesian in $K$.

Proof. Because there is exactly one abstract projection $f$ in $\mathcal{C}art_{\Phi/K}$, an extension of a functor $G : \mathcal{C} \to \mathcal{P}$ to some pre-expansion $\partial((\mathcal{C}art_{\Phi/K})_{/\Psi})$ is uniquely determined by a list of signed objects $\Psi$ in $\mathcal{P}$ such that $(GK^{\bullet}, \Psi)$ is admissible, together with a morphism $\widetilde{f} \in \mathcal{P}(G\Phi, \Psi)$. A further extension of this to the expansion $(\mathcal{C}art_{\Phi/K})_{/\Psi}$ consists of a morphism $\chi \in \mathcal{P}(GK^{\bullet}, \Psi)$ such that $\chi \circ Gf = \widetilde{f}$. Applying these characterizations to $\mathcal{Q}$ as well, we see that $G$ is $\pi$-extremal if and only if

For any list of signed objects $\Psi$ in $\mathcal{P}$ such that $(GK^{\bullet}, \Psi)$ is admissible, any morphism $\widetilde{f} \in \mathcal{P}(G\Phi, \Psi)$, and any morphism $\xi \in \mathcal{Q}(\pi GK^{\bullet}, \pi\Psi)$ such that $\xi \circ \pi Gf = \pi\widetilde{f}$, there exists a unique morphism $\chi \in \mathcal{P}(GK^{\bullet}, \Psi)$ such that $\chi \circ Gf = \widetilde{f}$ and $\pi(\chi) = \xi$.

However, this is also exactly what it means for (4.1) (with $f$ replaced by $Gf$) to be a pullback of sets, which is the definition of when $Gf$ is $\pi$-cartesian in $K$. $\square$

Our second important class of abstract cones is the following.

Definition 4.18. Let $\mathcal{A}$ be an ordinary small category, and let $\mathcal{A}^{\triangleright}$ denote the result of adjoining a new terminal object $T$. If we make $\mathcal{A}^{\triangleright}$ an LNL polycategory by declaring all objects to be linear, it becomes an abstract cone with vertex $T^{+}$. We denote this by $\mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}}$ and call it the **abstract linear colimit cone** determined by $\mathcal{A}$.

Dually, if $\mathcal{A}^{\circ}$ denotes the result of adjoining a new initial object $I$, then with all objects linear it yields an abstract cone with vertex $I^{-}$. We denote this by $\mathcal{L}im_{\mathcal{A}}^{\mathrm{L}}$ and call it an **abstract linear limit cone**.

Similarly, by declaring all the objects to be nonlinear, we obtain **abstract nonlinear colimit cones** $\mathcal{C}olim_{\mathcal{A}}^{\mathrm{NL}}$ and **abstract nonlinear limit cones** $\mathcal{L}im_{\mathcal{A}}^{\mathrm{NL}}$.

Observe that a concrete cone $G : \mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}} \to \mathcal{P}$ is determined by a cocone under a $\mathcal{A}$-shaped diagram in the category of linear objects of $\mathcal{P}$, and similarly in the other cases.

# Proposition 4.19.

(i) A concrete cone \( G: \mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}} \to \mathcal{P} \) is universal if and only if the corresponding cocone is a colimit, in the strong sense of (2.4).
(ii) A concrete cone \( G: \mathcal{L}im_{\mathcal{A}}^{\mathrm{L}} \to \mathcal{P} \) is universal if and only if the corresponding cocone is a limit, in the strong sense of (2.5).
(iii) A concrete cone \( G: \mathcal{C}olim_{\mathcal{A}}^{\mathrm{NL}} \to \mathcal{P} \) is universal if and only if the corresponding cocone is a colimit, in the strong sense of (2.2)-(2.3).
(iv) A concrete cone \( G: \mathcal{L}im_{\mathcal{A}}^{\mathrm{NL}} \to \mathcal{P} \) is universal if and only if the corresponding cocone is a limit in the sense of (2.1).