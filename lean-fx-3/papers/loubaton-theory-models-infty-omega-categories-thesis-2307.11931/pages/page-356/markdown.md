CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

of each other. For this consider the diagram

$$\begin{array}{c} \hom_D(u(a), b) \longrightarrow \hom_C(vu(a), v(b)) \xrightarrow{(\mu_a)_!} \hom_C(a, v(b)) \\ \Bigg\| \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \hom_D(uvu(a), uv(b)) \xrightarrow{(u(\mu_a))_!} \hom_D(u(a), uv(b)) \\ \Bigg\| \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \hom_D(u(a), b) \xrightarrow{(\epsilon_{u(a)})_!} \hom_D(uvu(a), b) \xrightarrow{(u(\mu_a))_!} \hom_D(u(a), b) \end{array}$$

which is commutative thanks to lemma 6.2.2.4 and the naturality of the hom. By hypothesis, the left lower horizontal morphism is equivalent to the identity. The outer square then defines an equivalence between $\psi \circ \phi$ and the identity. We show similarly $\phi \circ \psi \sim id$.

For the second assertion, remark that the composition

$$\hom_C(a, a') \to \hom_D(u(a), u(a')) \xrightarrow{\phi(a, u(a'))} \hom_C(a, vu(a'))$$

is by definition equivalent to

$$\hom_C(a, a') \to \hom_D(vu(a), vu(a')) \xrightarrow{(\mu_a)_!} \hom_C(a, vu(a'))$$

and according to the lemma 6.2.2.4, to

$$\hom_C(a, a') \xrightarrow{(\mu_{a'})_!} \hom_C(a, vu(a'))$$

The Yoneda lemma then implies that the unit of the adjunction is $\mu$. We proceed similarly for the counit.

**6.2.2.6.** In paragraph 6.1.4.4, for a morphism $i : I \to A^\sharp$ between marked $(\infty, \omega)$-categories, we define the morphism $i_! : \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$ and when $i$ is proper, a morphism $i_* : \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$.

**Corollary 6.2.2.7.** *Let $i : I \to A^\sharp$ be a morphism between U-small $(\infty, \omega)$-category. The functor $i^* : \underline{\mathrm{Hom}}(A, \underline{\omega}) \to \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega})$ has a left adjoint given by the functor $i_! : \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$. If $i$ is proper, the functor $i^*$ has a right adjoint $i_* : \underline{\mathrm{Hom}}_\ominus(I, \underline{\omega}) \to \underline{\mathrm{Hom}}(A, \underline{\omega})$.*

*Proof.* With the characterization of adjunction given in proposition 6.2.2.5, this is a direct consequence of natural transformations given in paragraph 6.1.4.4.

346