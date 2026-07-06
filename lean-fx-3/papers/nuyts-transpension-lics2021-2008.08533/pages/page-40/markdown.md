16:40

A. NUYTS AND D. DEVRIESE

Vol. 20:2

In practice, for concrete systems, we will want axioms based on our findings in Section 6.3, e.g. in a binary cubical system we would decree $\cdot \mid (i \in \partial \mathbb{I}) \leftrightarrow (i \equiv_{\mathbb{I}} 0) \vee (i \equiv_{\mathbb{I}} 1)$ where the latter two predicates could be axiomatized similarly to (8.1).

8.3. **Strictness axiom.** The strictness axiom [OP18] allows to extend a partial type $T$ to a total type if $T$ is isomorphic to a total type $A$, effectively strictifying the isomorphism:

$$\begin{array}{l} \mathbb{X} \mid \Gamma \vdash \varphi : \text{Prop} \quad \mathbb{X} \mid \Gamma \vdash A : \mathsf{U}_{\ell} \quad \mathbb{X} \mid \Gamma,_{-} : \varphi \vdash T : \mathsf{U}_{\ell} \quad \mathbb{X} \mid \Gamma,_{-} : \varphi \vdash i : A \cong T \\ \hline \mathbb{X} \mid \Gamma \vdash \text{Strict}\{A \cong (\varphi ? T ; i)\} : \mathsf{U}_{\ell} \quad \mathbb{X} \mid \Gamma \vdash \text{strict}\{\varphi ? i\} : A \cong \text{Strict}\{A \cong (\varphi ? T ; i)\} \\ \text{where } \Gamma,_{-} : \varphi \vdash \text{Strict}\{A \cong (\varphi ? T ; i)\} = T : \mathsf{U}_{\ell} \quad \Gamma,_{-} : \varphi \vdash \text{strict}\{\varphi ? i\} = i : A \cong T \end{array}$$

## 9. INVESTIGATING THE TRANSPENSION TYPE

In Section 2.2, we have briefly investigated the structure of a fully faithful transpension type in FFTraS. In this section, we investigate the structure of the general transpension type $\langle \langle [u] \mid A \rangle$ in MTraS.

9.1. **Poles.** Our first observation is that on the boundary, the transpension type is trivial. Let $\top : \mathbb{X}_1 \to \mathbb{X}_2$ be the modality, between any two modes, which maps any presheaf to the terminal presheaf. We clearly have $\top \circ \mu = \top$ for any $\mu$, but also $\mu \circ \top \cong \top$ because all internal modalities are right adjoints and therefore preserve the terminal object.

**Theorem 9.1** (Pole). *We have $\Omega[u \in \partial \mathbb{U}] \circ [\langle [u] \cong \top$. We can thus postulate a term $\mathbb{X}, u : \mathbb{U} \mid \Gamma,_{-} : u \in \partial \mathbb{U} \vdash \text{pole} : \langle [\langle [u] \mid T \rangle \text{ for any } \mathbb{X} \mid \Gamma, \widehat{\mathbf{Q}}_{[\langle [u] \mid T \rangle \text{ type}}, \text{ with an } \eta\text{-rule } \mathbb{X}, u : \mathbb{U} \mid \Gamma,_{-} : u \in \partial \mathbb{U} \vdash t = \text{pole} : \langle [\langle [u] \mid T \rangle$.*

*Sketch of proof.* The left adjoints $\forall (u : \mathbb{U}) \circ \Sigma(u \in \partial \mathbb{U})$ and $\perp$ of the concerned modalities are isomorphic because $\forall (u : \mathbb{U}).(u \in \partial \mathbb{U})$ is false. We give a full proof in the technical report [Nuy20b].

Definition 6.6 of the boundary relied on the notion of dimensional splitness. The following result shows that it was a good one: the transpension is *only* trivial on the boundary:

**Theorem 9.2** (Boundary). *In the model, we have* [Nuy20b]

$$\mathbb{X}, u : \mathbb{U} \mid \Gamma \vdash (u \in \partial \mathbb{U}) \cong \langle [\langle [u : \mathbb{U}] \mid \text{Empty} \rangle.$$

9.2. **Meridians.** As all our modalities are proper DRAs [BCM$^{+}$20], the modal introduction rule is invertible in the model. This immediately shows that sections$^{20}$ of the transpension type

$$\mathbb{X} \mid \Gamma \vdash f : \langle \forall (u : \mathbb{U}) \mid \langle [\langle [u : \mathbb{U}] \mid T \rangle \rangle$$

(which we call meridians) are in 1-1 correspondence with terms

$$\mathbb{X} \mid \Gamma, \widehat{\mathbf{Q}}_{[\langle [u] \mid T \rangle \vee u \circ [\langle [u] \mid T \rangle]} \vdash t : T.$$

If it were not for the locking of the context, this characterization in terms of poles and meridians would make the transpension type look quite similar to a dependent version of the suspension type in HoTT [Uni13], whence our choice of name. If $\mathbb{U}$ is $\top$-slice (hence

$^{20}$By a section of a dependent type, we mean a dependent function with the same domain as the type.