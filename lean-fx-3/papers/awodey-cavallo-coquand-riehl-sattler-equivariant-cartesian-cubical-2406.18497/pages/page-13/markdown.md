square (2.1.1) in which the $\mathfrak{F}$-algebra structure on $g^*f$ is induced from the $\mathfrak{F}$-algebra structure on $f$ as an $\mathfrak{F}$-morphism.

**Definition 2.1.2** ([Shu19, 3.2]). A notion of fibred structure $\psi \colon \mathfrak{F} \to \mathfrak{E}$ is **full** if $\mathfrak{F}(X) \to \mathfrak{E}(X)$ is fully faithful for each object $X$ of $\mathsf{E}$.^6

That is, $\mathfrak{F}$ is full if every pullback square between $\mathfrak{F}$-algebras uniquely extends to an $\mathfrak{F}$-morphism.

Shulman then axiomatizes various conditions associated to such a notion of fibred structure that can be used to build a classifying universe. The first of these conditions is the following:

**Definition 2.1.3** ([Shu19, 3.10]). A notion of fibred structure $\mathfrak{F}$ is **locally representable** if each pullback in the category of contravariant groupoid-valued pseudofunctors

$$\begin{array}{c} \bullet \xrightarrow{\quad} \mathfrak{F} \\ \downarrow \quad \downarrow \quad \downarrow \psi \\ \mathsf{E}(-, X) \xrightarrow[f]{} \mathfrak{E} \end{array}$$

is representable. Explicitly, every map $f \colon Y \to X$ has a *classifier* $\psi_f \colon \mathfrak{F}(f) \to X$ for $\mathfrak{F}$-algebra structures on $f$, meaning that that for all $g \colon Z \to X$, $\mathfrak{F}$-algebra structures on $g^*f$ correspond bijectively to lifts of $g$ through $\psi_f$, naturally in $g$:

$$\begin{array}{c} \mathfrak{F}(f) \\ \downarrow \quad \downarrow \psi_f \\ Z \xrightarrow[g]{} X. \end{array}$$

In particular, sections of the canonical map $\psi_f \colon \mathfrak{F}(f) \to X$ correspond uniquely to $\mathfrak{F}$-algebra structures on $f \colon Y \to X$.

**Lemma 2.1.4.** *Let $\mathfrak{F}$ be a locally representable notion of fibred structure.*

- (i) The pullback of any map $f \colon Y \to X$ along $\psi_f \colon \mathfrak{F}(f) \to X$ has a canonical $\mathfrak{F}$-algebra structure.
- (ii) If $g^*f$ is a pullback of $f$ along $g$, then $\mathfrak{F}(g^*f)$ is a pullback of $\mathfrak{F}(f)$ along $g$, i.e. $\mathfrak{F}(g^*f) \cong g^*\mathfrak{F}(f)$.

*Proof.* The top horizontal map in the pullback square

$$\begin{array}{c} \mathsf{E}(-, \mathfrak{F}(f)) \xrightarrow{\gamma_f} \mathfrak{F} \\ \downarrow \quad \downarrow \quad \downarrow \psi \\ \mathsf{E}(-, X) \xrightarrow[f]{} \mathfrak{E} \end{array}$$

specifies an $\mathfrak{F}$-algebra structure $\gamma_f$ on the map $\psi_f^*f$.

By pullback cancelation and fully faithfulness of the Yoneda embedding, local representability implies that the left-hand square is a pullback in contravariant groupoid-valued pseudofunctors and thus also in $\mathsf{E}$:

$$\begin{array}{c} \mathsf{E}(-, \mathfrak{F}(g^*f)) \xrightarrow{i_g} \mathsf{E}(-, \mathfrak{F}(f)) \xrightarrow{\gamma_f} \mathfrak{F} \\ \downarrow \quad \downarrow \quad \downarrow \psi_f \\ \mathsf{E}(-, Z) \xrightarrow[g]{} \mathsf{E}(-, X) \xrightarrow[f]{} \mathfrak{E}. \end{array}$$

^6 Shulman's definition asks that $\psi \colon \mathfrak{F} \to \mathfrak{E}$ is a subfunctor inclusion; this is equivalent because $\psi$ is a discrete fibration.

13