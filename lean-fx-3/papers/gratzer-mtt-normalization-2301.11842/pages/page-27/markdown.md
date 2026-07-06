Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:27

of pred, reflect, and reify collapse to singletons, while the type of code collapses to $\mathsf{Ty}_m(z)$ by Extension 2:

$$\alpha_{\bigcirc} : \prod_{z:\mathbf{syn}} T \cong \mathsf{Ty}_m(z)$$

$$\alpha_{\bigcirc}(z, A) = A.\mathsf{code}$$

Observe $(\mathsf{Ty}_m, \alpha_{\bigcirc}) : \sum_{A:\bigcirc U} \prod_{z:\mathbf{syn}} A(z) \cong T$, so the realignment axiom of Definition 4.6 applies and we can define

$$(\mathsf{Ty}_m^*, \alpha) = \mathsf{re}(T, \mathsf{Ty}_m, \alpha_{\bigcirc}) \tag{5.2}$$

The equation $z : \mathbf{syn} \vdash \mathsf{Ty}_m^* = \mathsf{Ty}_m(z)$ follows immediately from the second half of Definition 4.6. On elements $A : \mathsf{Ty}_m^*$, this implies $z : \mathbf{syn} \vdash A = \alpha(A).\mathsf{code}$. For readability, we continue to use record notation to manipulate $\mathsf{Ty}_m^*$.

Given $A : \mathsf{Ty}_m^*$, we define $\mathsf{Tm}_m^*(A)$:

$$\mathsf{Tm}_m^*(A) = A.\mathsf{pred} : \{\mathsf{U}_1 \mid z : \mathbf{syn} \mapsto \mathsf{Tm}_m(z, A)\} \tag{5.3}$$

To see that this is well-typed, we must show $\mathsf{Tm}_m^*(A) = \mathsf{Tm}_m(z, A)$ given $z : \mathbf{syn}$. The type of $A.\mathsf{code}$ in Construction 5.1 ensures $\mathsf{Tm}_m^*(A) = \mathsf{Tm}_m(z, A.\mathsf{code})$. We have observed that $A = A.\mathsf{code}$ under $z : \mathbf{syn}$ so $\mathsf{Tm}_m^*(A) = \mathsf{Tm}_m(z, A)$.

**Type connectives.** It remains only to close $(\mathsf{Ty}_m^*, \mathsf{Tm}_m^*)$ under all connectives in such a way that each connective lies over the corresponding one in $(\mathsf{Ty}_m, \mathsf{Tm}_m)$. For modelocal connectives, these constructions are very similar to those given by Sterling [Ste21] (Lemmas 5.8, 5.9, 5.10, and 5.11). Modal types and dependent products, however, involve modalities and thus are different than the other connectives (Lemmas 5.6 and 5.7).

**Lemma 5.6.** $(\mathsf{Ty}_m^*, \mathsf{Tm}_m^*)$ is closed under dependent products and the relevant constants lift those of $\mathsf{Ty}_m$ (i.e., under an assumption $z : \mathbf{syn}$, they agree with those of $\mathsf{Ty}_m$ and $\mathsf{Tm}_m$):

$$\mathsf{Prod}^* : (\mu \mid A : \mathsf{Ty}_n^*)(B : (\mu \mid \mathsf{Tm}_n^*(A)) \to \mathsf{Ty}_m^*) \to \mathsf{Ty}_m^*$$

$$\alpha_{\mathsf{Prod}^*} : (\mu \mid A : \mathsf{Ty}_n^*)(B : (\mu \mid \mathsf{Tm}_n^*(A)) \to \mathsf{Ty}_m^*)$$

$$\to \mathsf{Tm}_m^*(\mathsf{Prod}^*(A, B)) \cong [(\mu \mid a : \mathsf{Tm}_n^*(A)) \to \mathsf{Tm}_m^*(B(a))]$$

*Proof.* We must define two constants ($\mathsf{Prod}^*$ and $\alpha_{\mathsf{Prod}^*}$) with the aforementioned types. We begin by fixing $(\mu \mid A : \mathsf{Ty}_m^*)$ and $B : (\mu \mid \mathsf{Tm}_n^*(A)) \to \mathsf{Ty}_m^*$ and define $\Phi$ as follows:

$$\Phi = (\mu \mid a : \mathsf{Tm}_n^*(A)) \to \mathsf{Tm}_m^*(B(a))$$

Observe under $z : \mathbf{syn}$, the following equality holds:

$$\Phi = (\mu \mid a : \mathsf{Tm}_n(z, A)) \to \mathsf{Tm}_m(B(z, a))$$

We may apply realignment using $\alpha_{\mathsf{Prod}}(z) : \mathsf{Tm}_m(z, \mathsf{Prod}(z, A, B)) \cong \Phi$. This realignment yields a type $\Psi$ and isomorphism $\beta : \Psi \cong \Phi$. Under $z : \mathbf{syn}$, these restrict to $\mathsf{Tm}_m(z, \mathsf{Prod}(z, A, B))$ and $\alpha_{\mathsf{Prod}}(z)$ respectively.

With these to hand we define $\mathsf{Prod}^*$ and $\alpha_{\mathsf{Prod}^*}$ as follows:

$$\mathsf{Prod}^*(A, B).\mathsf{code} = \mathbf{Prod}(A.\mathsf{code}, \lambda v. B(\uparrow_A v).\mathsf{code})$$

$$\mathsf{Prod}^*(A, B).\mathsf{pred} = \Psi$$

$$\mathsf{Prod}^*(A, B).\mathsf{reflect} = \lambda e. \beta^{-1}(\lambda a. \uparrow_{B(a)} \mathbf{app}(e, \downarrow_A a))$$

$$\mathsf{Prod}^*(A, B).\mathsf{reify} = \lambda f. \mathbf{lam}(\lambda v. \downarrow_{B(\uparrow_A v)} \beta(f)(\uparrow_A v))$$

$$\alpha_{\mathsf{Prod}^*} = \beta$$