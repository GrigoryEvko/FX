CHAPTER 6. THE $(\infty, \omega)$-CATEGORY OF SMALL $(\infty, \omega)$-CATEGORIES

the downer square of the diagram of (6.1.3.27) factors as

$$\begin{array}{ccc} \iota_! \iota^* E \otimes [1]^\sharp & \longrightarrow & \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\mu_E) & \longrightarrow & \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\phi) \\ \uparrow & & \uparrow & & \uparrow \\ \iota_! \iota^* E \otimes \{1\} & \longrightarrow & \mathbf{L} \iota_! \iota^* E \otimes \{1\} & \xrightarrow[\mathbf{D}\hat{\phi}]{} & F \otimes \{1\} \end{array}$$

where $\mu_E$ denotes the canonical morphism $\iota_! \iota^* E \to \mathbf{L} \iota_! \iota^* E$. To conclude, one has to show that the lower left horizontal morphism is $\mu_E$. As these constructions are natural, and commute with the cartesian product with $B^\flat \to 1$ for $B$ an $(\infty, \omega)$-category, the lemma 6.1.3.20 implies the desired result. $\square$

**Lemma 6.1.3.28.** *The functor $\mathring{\partial}_{1,[a,1]}^c$ defined in (6.1.3.15) in is an equivalence.*

*Proof.* The lemma 6.1.3.26 induces a diagram

$$\begin{array}{ccc} \iota^* E \otimes \mathbf{F} h_1^{[1]} & \longrightarrow & \iota^* E \otimes \mathbf{F} h_0^{[1]} \\ \downarrow & & \downarrow \\ \iota^* F \otimes \mathbf{F} h_1^{[1]} & \longrightarrow & (\iota \otimes i d_{[1]})^* \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\phi) \end{array}$$

which corresponds to a natural transformation

$$\oint_{1,[a,1]} \phi \to (\iota \otimes i d_{[1]})^* \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\phi) \quad \longleftrightarrow \quad \phi \to \mathring{\partial}_{1,[a,1]}^c \int_{([a,1] \otimes [1]^\sharp)^\sharp} \xi(\phi)$$

Eventually, remark that proposition 6.1.3.10 and the equivalences (6.1.3.24) imply that this natural transformation is pointwise an equivalence. The functor (6.1.3.25) is then a left inverse of $\mathring{\partial}_{1,[a,1]}^c$. As it is an equivalence, so is $\mathring{\partial}_{1,[a,1]}^c$. $\square$

**Proposition 6.1.3.29.** *For any marked $(\infty, \omega)$-category $I$, and integer $n$, the morphism*

$$\mathring{\partial}_{n,I}^c : \text{LCart}((I \otimes [n]^\sharp)^\sharp) \to \text{Fun}^c([n], \text{LCart}(I))$$

*defined in (6.1.3.15) is an equivalence.*

*Proof.* Corollary 6.1.2.16, and propositions 5.1.2.1 and 6.1.3.13 imply that the two functors on $\Delta^{op} \times (\infty, \omega)\text{-cat}_m^{op}$:

$$\begin{aligned} (n, I) &\mapsto \text{LCart}^c(I \otimes [n]^\sharp) \\ (n, I) &\mapsto \text{Fun}^c([n], \text{LCart}^c(I)) \end{aligned}$$

send colimits to limits. We can then reduce to the case where $I$ is an element of $t\Theta$ and $n=1$. If $I$ is $[1]^\sharp$, remark that $\mathring{\partial}_{n,[1]^\sharp}^c$ is equivalent to $\mathring{\partial}_{n,[1]^\sharp}$ which is an equivalence according to proposition 6.1.3.11. If $I$ is of shape $[a,1]$ for $a$ in $t\Theta$, this is the content of lemma 6.1.3.28. $\square$

328