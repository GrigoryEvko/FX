Categorically, these rules mean we define the map $\mathsf{pr}^{\infty}_{\ell}: \mathsf{PSub}^{\infty}_{\ell} \to \mathsf{Tel}^{\infty}_{\ell}$ to be the limit of the sequence:

$$\cdots \to \mathsf{pr}_{\ell}^{n} \to \cdots \to \mathsf{pr}_{\ell}^{3} \to \mathsf{pr}_{\ell}^{2} \to \mathsf{pr}_{\ell} \to \mathbb{1}$$

where $\mathsf{pr}_{\ell}^{n}$ is the map such that

$$\mathsf{P}_{\mathsf{pr}_{\ell}^{n}} = \sum_{\forall i \leqslant n, \ell_{i} \leqslant \ell} \mathsf{P}_{\mathsf{pr}_{\ell_{0}}} \circ \cdots \circ \mathsf{P}_{\mathsf{pr}_{\ell_{n}}}.$$

In particular, $\mathsf{P}_{\mathbb{1}}$ is the identity functor and $\mathbb{1}$ is the identity map of the terminal object. There is only one natural map $\mathsf{pr}_{\ell}^{n+1} \to \mathsf{pr}_{\ell}^{n}$, which discards the last type in a telescope of length $n+1$; it is not possible to discard any of the other types and get a telescope of length $n$.

### 4.1.9 $\omega$-Limits

Finally, we define the structure of infinite (sequential, Reedy) limits on a CwF. These are an 'infinitary rule' (i.e. a non-elementary structure) that is not part of dTT or any implementable type theory, but we will use them to build our intended models of dTT. Syntactically, they are essentially just a kind of $\Sigma$-type of an infinite telescope.

**Definition 4.8.** A CwF with levels has $\omega$-limits if it is equipped with pullback squares

$$\begin{array}{ccc} \mathsf{PSub}_{\ell}^{\infty} & \xrightarrow{\lim} & \mathsf{Tm}_{\ell} \\ \mathsf{pr}^{\infty}_{\ell} \downarrow & \downarrow & \downarrow \mathsf{pr}_{\ell} \\ \mathsf{Tel}_{\ell}^{\infty} & \xrightarrow{\lim} & \mathsf{Ty}_{\ell}, \end{array}$$

In syntax, this means we have the following structure and properties. Firstly, having a merely commutative square as above gives the following rules:

$$\frac{\gamma : \Gamma \vdash \widetilde{\Upsilon} \gamma \mathsf{stel}_{\ell}^{\infty}}{\gamma : \Gamma \vdash \lim \left( \widetilde{\Upsilon} \gamma \right) \mathsf{type}_{\ell}}$$

$$\frac{\gamma : \Gamma \vdash \widetilde{\upsilon} \gamma : \widetilde{\Upsilon} \gamma}{\gamma : \Gamma \vdash \lim \left( \widetilde{\upsilon} \gamma \right) : \lim \left( \widetilde{\Upsilon} \gamma \right)}$$

Secondly,

$$\frac{\gamma : \Gamma \vdash u : \lim \left( \widetilde{\Upsilon} \gamma \right)}{\gamma : \Gamma \vdash \mathsf{res}^{\partial n} \gamma u : \widetilde{\Upsilon}^{\partial n} \gamma}$$

$$\frac{\gamma : \Gamma \vdash u : \lim \left( \widetilde{\Upsilon} \gamma \right)}{\gamma : \Gamma \vdash \mathsf{res}^{n} \gamma u : \widetilde{\Upsilon}^{n} \gamma \left( \mathsf{res}^{\partial n} \gamma u \right)}$$

We require that $\mathsf{res}^{\partial n}$ is derived from $\mathsf{res}^{n}$ via:

$$\begin{array}{l} \mathsf{res}^{\partial 0} \gamma u \equiv [ ] \\ \mathsf{res}^{\partial (n+1)} \gamma u \equiv [ \mathsf{res}^{\partial n} \gamma u, \mathsf{res}^{n} \gamma u ] \end{array}$$

and that the following computation and uniqueness rules hold:

$$\begin{array}{l} \mathsf{res}^{\partial n} \gamma \left( \lim \left( \widetilde{a} \gamma \right) \right) \equiv \widetilde{a}^{\partial n} \gamma \\ \mathsf{res}^{n} \gamma \left( \lim \left( \widetilde{a} \gamma \right) \right) \equiv \widetilde{a}^{n} \gamma \\ u \equiv \lim \left( \mathsf{res}^{n} \gamma u \right)_{n} \end{array}$$

50