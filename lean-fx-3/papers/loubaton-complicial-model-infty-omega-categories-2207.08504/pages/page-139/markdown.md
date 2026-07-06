3.3. COMPLICIAL SETS AS OF MODEL OF \((\infty, n)\)-CATEGORIES

Corollary 3.3.2.3. For any $n \in \mathbb{N}$, the adjunction constructed in 3.3.2.1

$$i_n : \mathrm{Psh}(\Theta_n \times \Delta) \xrightarrow{\perp} \mathrm{tPsh}(\Delta)^n : N_{i_n}$$

is a Quillen equivalence.

Proof. Note that $i_n$ preserves globes by construction. According to theorem 3.3.1.11, $\mathrm{tPsh}(\Delta)^n$ is a model of $(\infty, n)$-categories, and the proposition 3.1.3.4 concludes the proof. □

Construction 3.3.2.4. For any integer $n$, we have an Quillen adjunction

$$\mathrm{Psh}(\Theta_n \times \Delta) \xrightarrow[\leftarrow \tau_n]{\perp} \mathrm{Psh}(\Theta \times \Delta)$$

where the left adjoint is the left Kan extension of the canonical inclusion $\Theta_n \times \Delta \to \Theta \times \Delta$. The image of an object $X$ of $\mathrm{Psh}(\Theta_n \times \Delta)$ by $\iota$ will be simply denoted by $X$.

Theorem 3.3.2.5. For any $n \in \mathbb{N} \cup \{\omega\}$, the adjunction constructed in 3.3.2.1

$$i : \mathrm{Psh}(\Theta \times \Delta) \xrightarrow{\perp} \mathrm{tPsh}(\Delta)^\omega : N_i$$

is a Quillen equivalence. The model category $\mathrm{tPsh}(\Delta)^\omega$ is then a model of $(\infty, \omega)$-categories.

Proof. As the functor $i$ preserves globes, the theorem 2.4.2.9 implies that $N_i$ detects weak equivalences. To conclude the proof, it then remains to show that $i$ is homotopically fully faithfull.

Let $X$ be an element of $\mathrm{Psh}(\Theta \times \Delta)$. We have to show that the canonical morphism $X \to N_i \mathbf{F}iX$ is a weak equivalence where $\mathbf{F}$ is a fibrant replacement. The object $X$ is the colimit of the sequence

$$\tau_0 X \to \tau_1 X \to \tau_2 X \to \cdots$$

As the generating anodyne extension has finite codomain, the colimit of the sequence

$$\mathbf{F}i\tau_0 X \to \mathbf{F}i\tau_1 X \to \mathbf{F}i\tau_2 X \to \cdots$$

is a fibrant replacement of $iX$. As $N_i$ preserves directed colimits, and as $\tau_n N_i \cong N_{i_n}$, the object $N_i \mathbf{F}iX$ is the colimit of the sequence

$$N_{i_0} \mathbf{F}i_0\tau_0 X \to N_{i_1} \mathbf{F}i_1\tau_1 X \to N_{i_2} \mathbf{F}i_2\tau_2 X \to \cdots$$

As weak equivalences are stable by directed colimits, the corollary 3.3.2.3 implies that $X \to N_i \mathbf{F}iX$ is a weak equivalence, which concludes the proof. □

Finally, it may be useful to know the connection between the Quillen equivalences of Corollary 3.3.2.3 and Theorem 3.3.2.5 with the Street nerve defined in 2.2.3.1.

Construction 3.3.2.6. We denote by $\pi_0 : \mathrm{Psh}(\Theta_n \times \Delta) \to \mathrm{Psh}(\Theta_n)$ the left Kan extention of the functor sending $(a, [n])$ onto $a$. As $\pi_0$ sends W to isomorphisms, it induces an adjoint pair:

$$\pi_0 : \mathrm{Psh}(\Theta_n \times \Delta) \xrightarrow{\perp} (0, \omega)\text{-cat} : N_{\pi_0}$$

139