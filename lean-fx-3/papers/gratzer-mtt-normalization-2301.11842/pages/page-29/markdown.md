Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:29

$$b : (\nu \circ \mu \mid x : \mathsf{Tm}_n^*(A)) \to \mathsf{Tm}_o^*(B(\mathsf{m}_\mu^*(A, x)))$$

$$(\nu \mid p : \mathsf{Tm}_m^*(\mathsf{Mod}_\mu^*(A)))$$

We must construct an element of $\mathsf{Tm}_o^*(B(a))$. We begin by inspecting $p$. As MTT modalities in extensional MTT commute with dependent sums, equality, $\bullet$, and—by Extension 4—with finite coproducts, $p$ can be decomposed into the following:

$$(\nu \mid \mathsf{tm} : \mathsf{Nf}_m(\mathsf{Mod}_\mu(A)))$$

$$\mathsf{prf} : \bullet \begin{pmatrix} \sum_{e: \langle \nu | \mathsf{Ne}_m(\mathsf{Mod}_\mu(A)) \rangle} \mathsf{mod}_\nu(\mathsf{tm}) = \mathbf{up} \circledast e \\ + \sum_{a: \langle \nu \circ \mu | A.\mathsf{pred} \rangle} \mathsf{mod}_\nu(\mathsf{tm}) = (\mathbf{mod}_\mu \circ \downarrow_A) \circledast a \end{pmatrix}$$

Recall from Diagram 4.1 that $\bullet X$ is a pushout of **syn** and $X$. To define a map out of $\bullet X$, therefore, it suffices to define a map out of $X$ which is constant assuming $z : \mathbf{syn}$. We conclude by scrutinizing prf:

$$\begin{cases} \uparrow \mathsf{letmod}_{\mu;\nu}(A, \lambda v. B(\uparrow v).\mathsf{code}, \lambda x. \downarrow b(\uparrow x), e) & \text{if } \mathsf{prf} = \iota_1(\mathsf{mod}_\nu(e), \_) \\ b(a) & \text{if } \mathsf{prf} = \iota_2(\mathsf{mod}_\nu(a), \_) \end{cases}$$

Given $z : \mathbf{syn}$, both branches collapse to $\mathsf{letmod}_{\mu;\nu}(z, A, B, b, \mathsf{tm})$ so this yields a well-defined map. The boundary conditions follow from routine computations.

**Lemma 5.8.** $(\mathsf{Ty}_m^*, \mathsf{Tm}_m^*)$ is closed under dependent sums via:

$$\mathsf{Sig}^*(A, B) : \mathsf{Ty}_m^*$$

$$\alpha_{\mathsf{Sig}^*} : \mathsf{Tm}_m(\mathsf{Sig}^*(A, B)) \cong \sum_{a: \mathsf{Tm}_m^*(A)} \mathsf{Tm}_m^*(B(a))$$

Moreover, assuming $z : \mathbf{syn}$ then $\mathsf{Sig}^* = \mathsf{Sig}$ and $\alpha_{\mathsf{Sig}^*} = \alpha_{\mathsf{Sig}}$.

Proof. Fixing $A : \mathsf{Ty}_m^*$ and $B : \mathsf{Tm}_m^*(A) \to \mathsf{Ty}_m^*$. We begin by applying realignment to the following:

$$\left( \sum_{a: A.\mathsf{pred}} B(a).\mathsf{pred}, \alpha_{\mathsf{Sig}(z)} \right)$$

This produces $\Psi : \mathsf{U}_1$ and $\alpha_{\mathsf{Sig}^*} : \Psi \cong \sum_{a: A.\mathsf{pred}} B(a).\mathsf{pred}$ such that under the assumption $z : \mathbf{syn}$ the following holds:

$$\Psi = \mathsf{Tm}_m(\mathsf{Sig}(z, A, B)) \qquad \alpha_{\mathsf{Sig}^*} = \alpha_{\mathsf{Sig}}(z)$$

We now define $\mathsf{Sig}^*(A, B)$ as follows:

$$\mathsf{Sig}^*(A, B).\mathsf{code} = \mathbf{Sum}(A.\mathsf{code}, \lambda v. B.\mathsf{code}(\uparrow_A v))$$

$$\mathsf{Sig}^*(A, B).\mathsf{pred} = \Psi$$

$$\mathsf{Sig}^*(A, B).\mathsf{reflect} = \lambda e. \alpha_{\mathsf{Sig}^*}^{-1} \langle \uparrow_A(\mathbf{proj}_0(e)), \uparrow_{B(\uparrow_A(\mathbf{proj}_0(e)))} (\mathbf{proj}_1(e)) \rangle$$

$$\mathsf{Sig}^*(A, B).\mathsf{reify} = \lambda p. \mathbf{pair}(\downarrow_A(\alpha_{\mathsf{Sig}^*}p.0), \downarrow_{B(\alpha_{\mathsf{Sig}^*}p.0)} (\alpha_{\mathsf{Sig}^*}p.1))$$

The fact that $\downarrow$ and $\uparrow$ lie over the identity follows directly from the $\beta$ and $\eta$ laws of dependent sums in MTT. We show the calculations for $\uparrow$. Fix $z : \mathbf{syn}$:

$$\begin{aligned} \uparrow_{\mathsf{Sig}^*(A, B)}(e) &= \alpha_{\mathsf{Sig}^*}^{-1} \langle \uparrow_A(\mathbf{proj}_0(e)), \uparrow_{B(\uparrow_A(\mathbf{proj}_0(e)))} (\mathbf{proj}_1(e)) \rangle \\ &= \alpha_{\mathsf{Sig}}^{-1} \langle \mathbf{proj}_0(e), \mathbf{proj}_1(e) \rangle \\ &= \alpha_{\mathsf{Sig}}^{-1} \langle \alpha_{\mathsf{Sig}(A, B)}(e)_0, \alpha_{\mathsf{Sig}(A, B)}(e)_1 \rangle \\ &= e \end{aligned}$$