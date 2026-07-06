telescope rather than a type.

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} A \gamma \text{ type}_\ell}{\gamma : \Gamma \vdash_{\text{dm}} A_{\square(n+1)} \gamma \text{ tel}_\ell} \quad \frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{\text{dm}} t_{\square(n+1)} : A_{\square(n+1)} \gamma}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} A \gamma \text{ type}_\ell}{\text{pt}_{\square_n}^A : (\gamma : \Gamma, \square a : A_{\square(n+1)} \gamma) \to \Gamma}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} A \gamma \text{ type}_\ell}{\gamma : \Gamma, \square a : A_{\square(n+1)} \gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} z v_{\square_n}^A \gamma \square a : A^{[\text{pt}_{\square_n}^A, \mathbf{\Omega}_{\square_n}]} \gamma \square a}$$

These will satisfy the inductively proven property that for $\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} t \gamma : A \gamma$:

$$\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} z v_{\square_n}^A \gamma (t_{\square(n+1)} \gamma) \equiv t \gamma.$$

For $\text{sm}^{-2}$, the term $z v_{\square_{-2}}^A$ is trivial, since it lives in the terminal CwF structure. We also set:

$$A_{\square(-1)} \gamma \equiv ()_{\text{dm}}$$

$$t_{\square(-1)} \gamma \equiv []_{\text{dm}}$$

$$\text{pt}_{\square_{-2}}^A \equiv 1_\Gamma.$$

Note that, in general, since $z v_{\square_n}^A$ is a simplicial term, we may form its matching substitution:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square_n} \vdash_{\text{sm}^n} A \gamma \text{ type}_\ell}{\gamma : \Gamma, \square a : A_{\square(n+1)} \gamma \vdash_{\text{dm}} (z v_{\square_n}^A)_{\partial(n+1)} \gamma \square a : A_{\partial(n+1)} \gamma}$$

For $\text{sm}^{n+1}$ we then inductively set:

$$A_{\square(n+2)} \equiv (a : \pi A_{\square(n+1)} \gamma, a' : A_{n+1} \gamma ((z v_{\square_n}^{\pi A})_{\partial(n+1)} \gamma a)$$

$$t_{\square(n+2)} \equiv [t_{\square(n+1)}, t_{n+1}]$$

$$\text{pt}_{\square_{n+1}}^A \equiv \text{pt}_{\square_n}^{\pi A} \circ \text{pt}_{\text{dm}}^{A_{n+1}}$$

$$z v_{\square_{n+1}}^A \equiv \langle (z v_{\square_n}^{\pi A})^{[\text{pt}_{\text{dm}}^{A_{n+1}}, \mathbf{\Omega}_{\square}]}, (z v_{\square_{n+1}}^A)_{n+1} \rangle$$

$$(z v_{\square_{n+1}}^A)_{n+1} \gamma [a, a'] \equiv a'.$$

The second line is well typed by the inductive hypothesis and makes the next case of the hypothesis clear. Also, note the pt substitution in the fourth line. The basic idea is that, at the top dimension, the $(n+1)$-st simplicial value of a boxed variables access the last component of the modal context extension, whereas lower dimensional simplicial values search further back in the linear context.

We now move on to the untruncated model. The functor $\mathbf{\Omega}_{\square}$ in sm similarly constructs a constant presheaf. Note that $(\Gamma, \mathbf{\Omega}_{\square})^D \equiv (\Gamma, \mathbf{\Omega}_{\square})$, and $\rho_{\Gamma, \mathbf{\Omega}_{\square}}$ is an identity; we will omit writing these whenever the previous rules say that a $^D$ or $\rho$ is necessary. We now define a key natural transformation:

$$\mathbf{\Omega}_{\square}^{\triangle \square \leqslant 1_{\text{sm}}} : 1_{\text{sm}} \Rightarrow (-, \mathbf{\Omega}_{\triangle \square})$$

$$\left( \mathbf{\Omega}_{\square}^{\triangle \square \leqslant 1_{\text{sm}}} \right)_{m+1} \equiv \Gamma^{D^{m+1}}.$$

66