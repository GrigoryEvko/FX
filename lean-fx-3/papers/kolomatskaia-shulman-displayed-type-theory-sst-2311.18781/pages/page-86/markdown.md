We choose the level of the empty telescope $X^{\partial 0}$ to be $\ell \equiv \ell_0 \sqcup \ell_1$; the explicit description given below then implies that all the other telescopes $X^{\partial n}$ and $X^n$ are also at level $\ell$.

The object $X_{n+1}$ in section 4.5.1 corresponds to the telescope

$$(\phi : \Phi, \partial x : X^{\partial(n+1)} \phi) = (\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x).$$

Each morphism $x_{n+1} : X_{n+1} \to \overline{F}X_n$ such that $\epsilon \circ x_{n+1} = g_{n+1}$ then corresponds to a term

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x \vdash_{sm} \xi_n : F(X^{\partial n}) \phi \partial x.$$

By definition of $F$, $\xi_n$ is equivalent to two terms

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x \vdash_{sm} h_n \phi \partial x \, x : A \phi$$

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x, b : \mathcal{B} \phi (h_n \phi \partial x) \vdash_{sm} t_n \phi \partial x \, x \, b :$$

$$(X^{\partial n})^d \langle \phi, \sigma (h_n \phi \partial x) b \rangle \partial x.$$

The equation $Fg_{n+1} \circ x_{n+2} = x_{n+1} \circ g_{n+2}$ means that

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x, x' : X^{n+1} \phi [\partial x, x] \vdash_{sm} h_{n+1} \phi [\partial x, x] x' \equiv h_n \phi \partial x \, x$$

and

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x, x' : X^{n+1} \phi [\partial x, x], b : \mathcal{B} \phi (h_n \phi \partial x)$$

$$\vdash_{sm} t_{n+1} \phi [\partial x, x] x' \, b \equiv [t_n \phi \partial x \, x \, b, s_n \phi \partial x \, x \, x' \, b]$$

for some term

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x, x' : X^{n+1} \phi [\partial x, x], b : \mathcal{B} \phi (h_n \phi \partial x)$$

$$\vdash_{sm} s_n \phi \partial x \, x \, x' \, b : (X^n)^d \langle \phi, \sigma (h_n \phi \partial x) b \rangle \langle \partial x, t_n \phi \partial x \, x \, b \rangle x$$

$$\equiv (X^n)^d \langle \phi, \sigma (h_{n-1} \phi \partial x) b \rangle \langle \partial x, t_n \phi \partial x \, x \, b \rangle x$$

Now inspecting the actual construction, we start with $X_0 = X^{\partial 0} = \langle \rangle$, the empty telescope, and $X^0 = F(X^{\partial 0}) = F(\cdot) = A$. It is easy to see by induction that the functions $h_n$ then all just project to $X^0$. For the rest, combining eqs. (4.46) and (4.48), we find that $X^{n+1}$ is defined by

$$\phi : \Phi, \partial x : X^{\partial n} \phi, x : X^n \phi \partial x \vdash_{sm}$$

$$X^{n+1} \phi [\partial x, x] \equiv$$

$$(b : \mathcal{B} \phi (h_{n-1} \phi \partial x)) \to (X^n)^d \langle \phi, \sigma (h_{n-1} \phi \partial x) b \rangle \langle \partial x, t_n \phi \partial x \, x \, b \rangle x$$

and we have tautologically

$$s_n \phi \partial x \, x \, x' \, b \equiv x' \, b.$$

In particular, by induction we find that in fact each $X^n$, though by construction a telescope, is actually just a single type for all $n \geqslant 0$. Therefore, the tower $(X^{\partial n}, X^n)$ is precisely an infinite telescope as defined in section 4.1.8, which we denote

$$\bar{X} = (X^{\partial n}, X^n).$$

Our displayed coinductive type is therefore precisely the limit of this infinite telescope as in section 4.1.9:

$$\text{dCoind} [\Phi, A, \mathcal{B}, \sigma] \phi \equiv \lim \left( \bar{X} \phi \right).$$

86