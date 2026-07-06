6.1. UNIVALENCE

6.1.3.18. We fix an object $a$ of $t\Theta$. Let $E$ be an object of $\mathrm{LCart}([a, 1]^{\sharp})$. According to theorem 6.1.2.15, there exists a morphism $X(0) \times a^{\sharp} \to X(1)$ such that $E$ corresponds to the colimit

$$X(0)^{\flat} \times \mathbf{F} h_{0}^{[a^{\sharp}, 1]} \coprod_{X(0)^{\flat} \times a^{\flat}} X(1)^{\flat}$$

We claim that $\mathbf{L}\iota_{!} \mathbf{R}\iota^{*}E$ is the left cartesian fibration

$$X(0)^{\flat} \times (\mathbf{F} h_{0}^{[a^{\sharp}, 1]} \coprod_{a^{\flat}} (a \otimes [1]^{\sharp})^{\flat}) \coprod_{X(0)^{\flat} \times (a \otimes \{1\})^{\flat}} X(1)^{\flat} \tag{6.1.3.19}$$

Indeed, the lemma 6.1.3.17 provides an initial morphism from $\iota_{!} \mathbf{R}\iota^{*}E$ to this object, and the theorem 5.2.3.3 implies that this object is a left cartesian fibration.

Lemma 6.1.3.20. Let $\psi : \iota_{!} \mathbf{R}\iota^{*} \to \mathbf{L}\iota_{!} \mathbf{R}\iota^{*}$ be a natural transformation, endowed with a family of natural commutative squares:

$$\begin{array}{ccc} \iota_{!} \mathbf{R}\iota^{*}(B^{\flat} \times E) & \xrightarrow{\psi_{B^{\flat} \times E}} & \mathbf{L}\iota_{!} \mathbf{R}\iota^{*}(B^{\flat} \times E) \\ \downarrow & & \downarrow \\ B^{\flat} \times \iota_{!} \mathbf{R}\iota^{*}E & \xrightarrow[B^{\flat} \times \psi_{E}]{} & B^{\flat} \times \iota_{!} \mathbf{R}\iota^{*}E \end{array}$$

where we identify marked $(\infty, \omega)$-categories with their canonical morphisms to the terminal marked $(\infty, \omega)$-category. The natural transformation $\psi$ is then the one obtained by the functorial factorization in initial morphisms followed by left cartesian fibrations.

Proof. The natural transformation $\psi$ induces a natural transformation $\mathbf{D}\psi : \mathbf{L}\iota_{!} \mathbf{R}\iota^{*} \to \mathbf{L}\iota_{!} \mathbf{R}\iota^{*}$ and we have to check that this last natural transformation is the identity. The explicit Grothendieck construction states that $E$ is a colimit of left cartesian fibration of shape $B^{\flat} \times \mathbf{F} h_{\epsilon}^{[a^{\sharp}, 1]}$ for $\epsilon \in \{0, 1\}$. The hypothesis implies that we just have to show that $\mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}$ and $\mathbf{D}\psi_{\mathbf{F} h_{1}^{[a^{\sharp}, 1]}}$ are equivalences, and we will check this on fibers.

Using the explicit expression of $\mathbf{L}\iota_{!} \mathbf{R}\iota$ given in (6.1.3.19), we have equivalences

$$\{0\}^{*} \mathbf{L}\iota_{!} \mathbf{R}\iota \mathbf{F} h_{0}^{[a^{\sharp}, 1]} \sim 1 \qquad \{0\}^{*} \mathbf{L}\iota_{!} \mathbf{R}\iota \mathbf{F} h_{1}^{[a^{\sharp}, 1]} \sim \emptyset \qquad \{1\}^{*} \mathbf{L}\iota_{!} \mathbf{R}\iota \mathbf{F} h_{0}^{[a^{\sharp}, 1]} \sim 1$$

which directly implies that $\{0\}^{*} \mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}$, $\{0\}^{*} \mathbf{D}\psi_{\mathbf{F} h_{1}^{[a^{\sharp}, 1]}}$ and $\{1\}^{*} \mathbf{D}\psi_{\mathbf{F} h_{1}^{[a^{\sharp}, 1]}}$ are equivalences. The only case remaining is $\{1\}^{*} \mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}$. This morphism corresponds to an endomorphism of $(a \otimes [1]^{\sharp})^{\sharp}$, which is a strict object according to 5.1.3.20. By right cancellation, the morphism induced by the domain of $\mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}$ is a left cartesian fibration. There exists then a lift in the following diagram

$$\begin{array}{ccc} \{0\} & \longrightarrow & [a, 1]_{0/}^{\sharp} \coprod_{a^{\flat} \otimes \{0\}} (a \otimes [1]^{\sharp})^{\flat} \\ \downarrow & \longmapsto & \downarrow^{\operatorname{dom} \mathbf{D}\psi_{\mathbf{F} h_{0}^{[a^{\sharp}, 1]}}} \\ [a, 1]_{0/}^{\sharp} & \xrightarrow{\iota} & [a, 1]_{0/}^{\sharp} \coprod_{a^{\flat} \otimes \{0\}} (a \otimes [1]^{\sharp})^{\flat} \end{array} \tag{6.1.3.21}$$

325