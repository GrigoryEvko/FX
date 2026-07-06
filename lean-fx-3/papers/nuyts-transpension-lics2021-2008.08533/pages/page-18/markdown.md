16:18

A. NUYTS AND D. DEVRIESE

Vol. 20:2

For example, in Section 6, we will come up with a modality $\mathfrak{g}[u]$ for the transpension, and then the introduction rule WDRA:INTRO will take the form

$$\frac{p \mid \Delta, \mathbf{\Omega}_{\mathfrak{g}[u]} \vdash t : T}{q \mid \Delta \vdash \text{mod}_{\mathfrak{g}[u]} t : \langle \mathfrak{g}[u] \mid T \rangle}$$

for certain modes $p$ and $q$, which is quite reminiscent of the introduction rule of the transpension type in FFTraS (Section 2) if you bear in mind that $[\mathbf{\Omega}_{\mathfrak{g}[u]}]$ is essentially $\forall u$.

Instead of littering this paper with remarks of the form 'recall that $[\mathbf{\Omega}_{\mu}] = \ldots'$, we will decorate locks, keys and variables with superscript reminders of the left adjoints to the modalities (and 2-cells mediating them) that are already in subscript. Concretely, we will assign:

- to every modality $\mu : p \to q$ a left name $\kappa : q \to p$ (writing this succinctly as $\kappa \dashv \mu : p \to q$),
- to every 2-cell $\alpha : \mu \Rightarrow \mu'$ a left name $\omega : \kappa' \Rightarrow \kappa$ (where $\kappa \dashv \mu$ and $\kappa' \dashv \mu'$; writing succinctly $\kappa \Leftarrow \kappa' : \omega \dashv \alpha : \mu \Rightarrow \mu'$).

Of course if $\kappa' \dashv \mu'$ and $\kappa \dashv \mu$, then the composite will be $\kappa \circ \kappa' \dashv \mu' \circ \mu$. If a modality $\mu$ has a left adjoint modality $\nu$, then we will always use $\nu$ as the left name of $\mu$, and similar for 2-cells. Then, we can write $\mathbf{\Omega}_{\mu}^{\kappa}$ for $\mathbf{\Omega}_{\mu}$, and $\mathbf{\alpha}_{\alpha:\mu\Rightarrow\mu'}^{\omega:\kappa'\Rightarrow\kappa}$ or just $\mathbf{\alpha}_{\alpha}^{\omega}$ for $\mathbf{\alpha}_{\alpha:\mu\Rightarrow\mu'}$, and $x_{\alpha:\mu\Rightarrow\mu'}^{\omega:\kappa'\Rightarrow\kappa}$ or just $x_{\alpha}^{\omega}$ for $x_{\alpha:\mu\Rightarrow\mu'}$. Note that we have

$$(\Gamma, \mathbf{\Omega}_{\mu_1}^{\kappa_1}, \mathbf{\Omega}_{\mu_2}^{\kappa_2}) = (\Gamma, \mathbf{\Omega}_{\mu_1 \circ \mu_2}^{\kappa_2 \circ \kappa_1}), \quad (\sigma, \mathbf{\alpha}_{\alpha_1}^{\omega_1}, \mathbf{\alpha}_{\alpha_2}^{\omega_2}) = (\sigma, \mathbf{\alpha}_{\alpha_1 * \alpha_2}^{\omega_2 * \omega_1}), \quad a[\mathbf{\alpha}_{\alpha}^{\omega}][\mathbf{\alpha}_{\beta}^{\psi}] = a[\mathbf{\alpha}_{\beta \circ \alpha}^{\omega \circ \psi}]. \tag{3.1}$$

3.5. Results. We highlight some results about MTT that are relevant in the current paper.

Proposition 3.1. We have $\langle 1 \mid A \rangle \cong A$ and $\langle \nu \circ \mu \mid A \rangle \cong \langle \nu \mid \langle \mu \mid A \rangle \rangle$.

Proposition 3.2. For any 2-cell $\alpha : \mu \Rightarrow \nu$, we have $\langle \mu \mid A \rangle \to \langle \nu \mid A[\mathbf{\alpha}_{\alpha}] \rangle$.

Proposition 3.3 (Projection). If $\kappa \dashv \mu$ internal to the mode theory, with unit $\eta : 1 \Rightarrow \mu \circ \kappa$ and co-unit $\varepsilon : \kappa \circ \mu \Rightarrow 1$, then there is a function $\varepsilon : (\kappa \mid \langle \mu \mid A \rangle) \to A[\mathbf{\alpha}_{\varepsilon}]$, satisfying a $\beta$-and (thanks to extensionality) an $\eta$-law:

$$\varepsilon \cdot_{\kappa} (\text{mod}_{\mu} a) = a[\mathbf{\alpha}_{\varepsilon}], \qquad \hat{a} = \text{mod}_{\mu} (\varepsilon \cdot_{\kappa} (\hat{a}[\mathbf{\alpha}_{\eta}])).$$

Combined with these rules, $\varepsilon$ is equally expressive as the let-eliminator for $\langle \mu \mid \sqcup \rangle$.

Proposition 3.4 (Internal transposition). Let $\kappa \dashv \mu$ internal to the mode theory, with unit $\eta : 1 \Rightarrow \mu \circ \kappa$ and co-unit $\varepsilon : \kappa \circ \mu \Rightarrow 1$. Adding left names, we get $\zeta \dashv \kappa \dashv \mu$ with $1 \Leftarrow \zeta \circ \kappa : \varepsilon' \dashv \eta : 1 \Rightarrow \mu \circ \kappa$ and $\kappa \circ \zeta \Leftarrow 1 : \eta' \dashv \varepsilon : \kappa \circ \mu \Rightarrow 1$.

Then there is an isomorphism of contexts expressing that $\kappa$ respects context extension:

$$\sigma = (x_{\eta}^{\varepsilon'} / y) : (\Gamma, x : A, \mathbf{\Omega}_{\mu}^{\kappa}) \cong (\Gamma, \mathbf{\Omega}_{\mu}^{\kappa}, \kappa \mid y : A[\mathbf{\alpha}_{\eta}^{\varepsilon'}]).$$