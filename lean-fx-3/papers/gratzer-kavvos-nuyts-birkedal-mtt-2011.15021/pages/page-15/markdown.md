Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:15

$$\boxed{\Gamma \vdash A \text{ type}_\ell @ m}$$

$$\frac{\Gamma \text{ ctx } @ m}{\Gamma \vdash \mathbb{B} \text{ type}_\ell @ m}$$

$$\frac{\Gamma \text{ ctx } @ m}{\Gamma \vdash U \text{ type}_1 @ m}$$

$$\frac{\Gamma \text{ ctx } @ m \quad \Gamma \vdash M : U @ m}{\Gamma \vdash \text{El}(M) \text{ type}_0 @ m}$$

$$\frac{\ell \leq \ell' \quad \Gamma \text{ ctx } @ m \quad \Gamma \vdash A \text{ type}_\ell @ m}{\Gamma \vdash \upharpoonright A \text{ type}_{\ell'} @ m}$$

$$\frac{\Gamma \text{ ctx } @ m \quad \Gamma \vdash A \text{ type}_\ell @ m \quad \Gamma \vdash M, N : \upharpoonright A @ m}{\Gamma \vdash \text{Id}_A(M, N) \text{ type}_\ell @ m}$$

$$\frac{\Gamma \text{ ctx } @ m \quad \mu : \text{Hom}_{\mathcal{M}}(n, m) \quad \Gamma \bullet_\mu \vdash A \text{ type}_\ell @ n}{\Gamma \vdash \langle \mu \mid A \rangle \text{ type}_\ell @ m}$$

$$\frac{\mu : \text{Hom}_{\mathcal{M}}(n, m) \quad \Gamma \text{ ctx } @ m \quad \Gamma \bullet_\mu \vdash A \text{ type}_\ell @ n \quad \Gamma .(\mu \mid \upharpoonright A) \vdash B \text{ type}_\ell @ m}{\Gamma \vdash (\mu \mid A) \to B \text{ type}_\ell @ m}$$

$$\frac{\Gamma \text{ ctx } @ m \quad \Gamma \vdash A \text{ type}_\ell @ m \quad \Gamma .(1 \mid \upharpoonright A) \vdash B \text{ type}_\ell @ m}{\Gamma \vdash \sum(A, B) \text{ type}_\ell @ m}$$

$$\frac{\Gamma, \Delta \text{ ctx } @ m \quad \Delta \vdash A \text{ type}_\ell @ m \quad \Gamma \vdash \delta : \Delta @ m}{\Gamma \vdash A[\delta] \text{ type}_\ell @ m}$$

Figure 4: MTT Types

$$\boxed{\Gamma \vdash \delta : \Delta @ m}$$

$$\frac{\Gamma \text{ ctx } @ m}{\Gamma \vdash \cdot : \cdot @ m}$$

$$\frac{\Gamma \text{ ctx } @ n \quad \mu : \text{Hom}_{\mathcal{M}}(n, m) \quad \Gamma \bullet_\mu \vdash A \text{ type}_1 @ n}{\Gamma .(\mu \mid A) \vdash \uparrow : \Gamma @ m}$$

$$\frac{\Gamma \text{ ctx } @ m}{\Gamma \vdash \text{id} : \Gamma @ m}$$

$$\frac{\Gamma, \Delta, \Xi \text{ ctx } @ m \quad \Gamma \vdash \gamma : \Delta @ m \quad \Delta \vdash \delta : \Xi @ m}{\Gamma \vdash \delta \circ \gamma : \Xi @ m}$$

$$\frac{\Gamma, \Delta \text{ ctx } @ m \quad \mu : \text{Hom}_{\mathcal{M}}(n, m) \quad \Gamma \vdash \delta : \Delta @ m}{\Gamma \bullet_\mu \vdash \delta \bullet_\mu : \Delta \bullet_\mu @ n}$$

$$\frac{\Gamma \text{ ctx } @ m \quad \mu, \nu : \text{Hom}_{\mathcal{M}}(n, m) \quad \alpha : \nu \Rightarrow \mu}{\Gamma \bullet_\mu \vdash \mathfrak{A}_\Gamma^\alpha : \Gamma \bullet_\nu @ n}$$

$$\frac{\Gamma, \Delta \text{ ctx } @ m \quad \Gamma \vdash \delta : \Delta @ m \quad \mu : \text{Hom}_{\mathcal{M}}(n, m) \quad \Delta \bullet_\mu \vdash A \text{ type}_1 @ n \quad \Gamma \bullet_\mu \vdash M : A[\delta \bullet_\mu] @ n}{\Gamma \vdash \delta . M : \Delta .(\mu \mid A) @ m}$$

Figure 5: MTT Substitutions