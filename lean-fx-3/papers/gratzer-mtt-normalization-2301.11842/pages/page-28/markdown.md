27:28

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

It remains to check a variety of boundary conditions under $z : \mathbf{syn}$. In particular, we must show that $\operatorname{Prod}^*(A, B) = \operatorname{Prod}(z, A, B)$ and that reflect and reify become the identity. These follow directly from assumptions about $A$, $B$, and the boundaries of various constructors. For instance

$$\begin{array}{l} \operatorname{Prod}^*(A, B) = \operatorname{Prod}^*(A, B).\text{code} \\ = \operatorname{Prod}(A.\text{code}, \lambda v. B(\downarrow_A v).\text{code}) \\ = \operatorname{Prod}(z, A.\text{code}, \lambda v. B(\downarrow_A v).\text{code}) \\ = \operatorname{Prod}(z, A, \lambda v. B(\downarrow_A v)) \\ = \operatorname{Prod}(z, A, B) \end{array}$$

Lemma 5.7. $(\mathsf{Ty}_m^*, \mathsf{Tm}_m^*)$ is closed under modal types and the four relevant constants $(\mathsf{Mod}_\mu^*, \mathsf{m}_\mu^*, \mathsf{letmod}_{\mu;\nu}^*, \text{and } \mathsf{Mod}/\mathsf{beta}_{\mu;\nu}^*)$ lift those of their counterparts in $\mathsf{Ty}_m$ and $\mathsf{Tm}_m$.

Proof. Fix a modality $\mu : n \longrightarrow m$. In this case we define the four constants $\mathsf{Mod}_\mu$, $\mathsf{m}_\mu$, $\mathsf{letmod}_{\mu;\nu}$, and $\mathsf{Mod}/\mathsf{beta}_{\mu;\nu}$ described in Section 3.1, subject to the expected boundary conditions. Fix a variable $A : \mathsf{Ty}_n^*$ under the modal annotation $\mu$ i.e., $(\mu \mid A : \mathsf{Ty}_n^*)$. We define the unaligned predicate as follows:

record $\Phi : \mathsf{U}_1$ where

$\mathsf{tm} : \mathsf{Nf}_m(\mathsf{Mod}_\mu(A))$

$\mathsf{prf} : \bullet \left( \begin{array}{l} \sum_{e: \mathsf{Ne}_m(\mathsf{Mod}_\mu(A))} \mathsf{tm} = \mathbf{up}(e) \\ + \sum_{a: (\mu|A.\mathsf{pred})} \mathsf{tm} = \mathbf{mod}_\mu(\downarrow_A a) \end{array} \right)$

For the first time, we have used the closed modality $\bullet$ to explicitly tweak the proof-relevant predicate. Intuitively, $\Phi$ is a predicate on $\mathsf{Tm}_m(z, \mathsf{Mod}_\mu(z, A))$ and $\mathsf{tm}$ ensures that this predicate tracks elements with normals forms. The second field, moreover, ensures that these normal are either neutral or $\mathsf{mod}_\mu(a)$ where $a$ is computable. Without the closed modality shielding the second field of $\Phi$, however, this could never have the correct extent along $z : \mathbf{syn}$. Using $\bigcirc \bullet X \cong \mathbf{1}$ and the boundary of $\mathsf{Nf}_m(\mathsf{Mod}_\mu(A))$, we can now define the following isomorphism:

$$\alpha_\bigcirc(z, p) = p.\mathsf{tm} : \prod_{z: \mathbf{syn}} \Phi \cong \mathsf{Tm}_m(z, \mathsf{Mod}_\mu(z, A))$$

Realigning $\Phi$ along $\alpha_\bigcirc$, we obtain $\Psi$ and $\alpha : \Psi \cong \Phi$ which under $z : \mathbf{syn}$ become $\mathsf{Tm}_m(z, \mathsf{Mod}_\mu(z, A))$ and $\alpha_\bigcirc$.

We now define $\mathsf{Mod}_\mu^*$:

$$\mathsf{Mod}_\mu^*(A).\text{code} = \mathbf{Mod}_\mu(A.\text{code})$$

$$\mathsf{Mod}_\mu^*(A).\text{pred} = \Psi$$

$$\mathsf{Mod}_\mu^*(A).\text{reflect} = \lambda e. \alpha^{-1} \langle \mathbf{up}(e), \eta_\bullet \iota_1 \langle e, \star \rangle \rangle$$

$$\mathsf{Mod}_\mu^*(A).\text{reify} = \lambda m. \alpha(m).\mathsf{tm}$$

Unlike Lemma 5.6, the introduction and elimination principles are not automatically obtained from $\alpha$ and they must be constructed separately:

$$\mathsf{m}_\mu^*(A, a) = \alpha^{-1} \langle \mathbf{mod}_\mu(\downarrow_A a), \eta_\bullet \iota_2 \langle a, \star \rangle \rangle$$

It remains to define the elimination principle $\mathsf{letmod}_{\mu;\nu}^*$. This is an involved affair and we describe it step-by-step. Begin by fixing $\nu : m \longrightarrow o$ along with the following:

$$B : (\nu \mid \mathsf{Tm}_m^*(\mathsf{Mod}_\mu^*(A))) \to \mathsf{Ty}_o$$