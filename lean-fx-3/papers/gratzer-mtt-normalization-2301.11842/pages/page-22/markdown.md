27:22

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

considering a pair of presheaf cosmoi for the mode theory $\{\mu : n \longrightarrow m\}$ and a 2-natural transformation of right adjoints between them:

$$\begin{array}{c} \mathcal{E}_n \xrightarrow{\rho_n} \mathcal{F}_n \\ f \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathcal{E}_m \xrightarrow{\rho_m} \mathcal{F}_m \end{array} \tag{4.3}$$

For simplicity and since we do not require the additional generality, we shall assume that $F$ and $G$ are strict 2-functors and that the 2-natural transformation between them is likewise strict. Let us further assume that $f$ and $g$ preserve finite colimits.

Gluing 'horizontally', we obtain a pair of categories $\mathbf{Gl}(\rho_n)$ and $\mathbf{Gl}(\rho_m)$ and by Theorems 4.3 and 4.8 both are presheaf topoi and models of STC. Artin gluing is functorial, and Diagram 4.3 induce a functor $\mathbf{Gl}(f, g) : \mathbf{Gl}(\rho_n) \longrightarrow \mathbf{Gl}(\rho_m)$ sending $(E_n, F_n, x)$ to $(f(E_n), g(F_n), g(x))$.

**Lemma 4.9.** $\mathbf{Gl}(f, g) : \mathbf{Gl}(\rho_n) \longrightarrow \mathbf{Gl}(\rho_m)$ is a right adjoint.

*Proof.* While this follows classically from the special adjoint functor theorem, an explicit construction is useful. There is a comparison $\beta : g_! \circ \rho_m \longrightarrow \rho_n \circ f_!$ induced by transposition and the unit of the $f_! \dashv f$. The left adjoint $\mathbf{Gl}(f, g)_!$ sends $f : F \longrightarrow \rho_m(E)$ to $\beta \circ g_!(f) : g_!(F) \longrightarrow \rho_n(f_!(E))$. The isomorphism $[[f, g]_!(X), Y] \cong X, f, g]$ is given component-wise by the isomorphisms associated with $f_! \dashv f$ and $g_! \dashv g$. $\square$

**Remark 4.10.** This explicit calculation show that $\pi_n : \mathbf{Gl}(\rho_n) \longrightarrow \mathcal{E}_n$ and $\pi_m : \mathbf{Gl}(\rho_m) \longrightarrow \mathcal{E}_m$ assemble into a natural transformation which satisfies Beck-Chevalley.

Since each $\mathbf{Gl}(\rho_-)$ is a presheaf topos, it supports a model of extensional type theory. We wish to stitch these models together into a single model of MTT with mode theory $\{n \longrightarrow m\}$ using the results of Gratzer et al. [GKNB21]. To do so, we must show that $\mathbf{Gl}(f, g)$ induces a dependent right adjoint between models of MLTT in $\mathbf{Gl}(\rho_n)$ and $\mathbf{Gl}(\rho_m)$. Next, we show this holds if we take the models of extensional type theory in $\mathbf{Gl}(\rho_-)$ as each having universes of types given by a sufficiently large Hofmann–Streicher universe:

**Lemma 4.11.** The adjunction $\mathbf{Gl}(f, g)_! \dashv \mathbf{Gl}(f, g)$ induces a dependent right adjoint with respect to sufficiently large Hofmann–Streicher universe $\mathcal{U}$.

*Proof.* It suffices to argue that $\mathbf{Gl}(f, g)$ sends a $\mathcal{U}$-small family in $\mathbf{Gl}(\rho_n)$ to a $\mathcal{U}$-small in $\mathbf{Gl}(\rho_m)$. This is proven by e.g., Gratzer et al. [GSS22, Lemma 3.3.7]. $\square$

As a consequence of Lemma 4.11, we obtain a model of MTT with the mode theory $\{\mu : n \longrightarrow m\}$ which interprets $n$, $m$, and $\mu$ as $\mathbf{Gl}(\rho_n)$, $\mathbf{Gl}(\rho_m)$, and $\mathbf{Gl}(f, g)$ respectively. This model of MTT is particularly well-behaved: equality is extensional and $\mathbf{Gl}(f, g)$ validates the strong transposition-style elimination rules specified by Birkedal et al. [BCM$^+$20].

**Lemma 4.12.** In this model of MTT, $\langle \mu \mid \mathbf{syn}_n \rangle \cong \mathbf{syn}_m$

*Proof.* Externally, $\mathbf{syn}_n = (\mathbf{1}, \mathbf{0}, !)$ but $g$ preserves $\mathbf{0}$ while $f$ preserves $\mathbf{1}$, so $\mathbf{Gl}(f, g)(\mathbf{syn}_n) \cong (\mathbf{1}, \mathbf{0}, !) = \mathbf{syn}_m$. $\square$

**Lemma 4.13.** In this model of MTT, $\bigcirc \langle \mu \mid A \rangle \cong \langle \mu \mid \bigcirc A \rangle$ and $\bullet \langle \mu \mid A \rangle \cong \langle \mu \mid \bullet A \rangle$.