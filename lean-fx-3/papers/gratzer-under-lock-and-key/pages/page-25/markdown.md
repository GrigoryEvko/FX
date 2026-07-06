With lock weakening at hand, we define a metatheoretic operation

$$N[\Gamma; M/x]$$

which stands for the *substitution* of $M$ for the variable $x$ under context $\Gamma$. In most cases this operation simply recurses appropriately through the structure of the term. The novel clauses are

$$\begin{aligned} &x^{\alpha}[\Gamma; M/x] \stackrel{\text{def}}{=} M[\Gamma; \alpha; \cdot] \\ &\text{mod}_{\xi}(N)[\Gamma; M/x] \stackrel{\text{def}}{=} \text{mod}_{\xi}(N[\Gamma; M/x]) \\ &(\text{let}_{\rho} \text{ mod}_{\xi}(y_A) \leftarrow N_0 \text{ in } N_1)[\Gamma; M/x] \stackrel{\text{def}}{=} \text{let}_{\rho} \text{ mod}_{\xi}(y_A) \leftarrow N_0[\Gamma; M/x] \text{ in } N_1[\Gamma; M/x] \end{aligned}$$

The rest of the clauses are according to custom. Notice that $\Gamma$ is a global parameter to this definition, and is only used in the base case in order to effect lock weakening.

**Theorem 5.3** (Cut). *The following rule is admissible:*

$$\frac{\Gamma, \widehat{\bullet}_{\mu} \vdash M : A \circledcirc n \quad \Gamma, x : (\mu \mid A), \Delta \vdash N : B \circledcirc b}{\Gamma, \Delta \vdash N[\Gamma; M/x] : B \circledcirc b}$$

*Proof.* By induction on the derivation of $\Gamma, x : (\mu \mid A), \Delta \vdash N : B \circledcirc b$. We show only the modal cases, the rest being according to custom.

$\text{CASE}(\Gamma, x : (\mu \mid A), \Delta \vdash x^{\alpha} : A \circledcirc b)$.

Writing $\mu : n \rightarrow m$, we have $\alpha : \mu \Rightarrow \text{locks}(\Delta)$, and hence $b = n$. By **Theorem 5.2** we have that

$$\Gamma, \widehat{\bullet}_{\text{locks}(\Delta)} \vdash M[\Gamma; \alpha; \cdot] : A \circledcirc n$$

Hence, by repeatedly using the equation $\Gamma, \widehat{\bullet}_{\mu}, \widehat{\bullet}_{\nu} = \Gamma, \widehat{\bullet}_{\mu \circ \nu} \text{ ctx } \circledcirc o$ on the context to unfuse the locks into the right arrangement, followed by repeated applications of the weakening rule **VARWK** shown admissible in **Theorem 5.1**, we deduce that

$$\Gamma, \Delta \vdash M[\Gamma; \alpha; \cdot] : A \circledcirc n$$

But as this is the definiens of $x^{\alpha}[\Gamma; M/x]$ we obtain the conclusion.

$\text{CASE}(\Gamma, x : (\mu \mid A), \Delta \vdash \text{mod}_{\xi}(N) : \langle \xi \mid A \rangle \circledcirc b)$.

Writing $\xi : a \rightarrow b$, we know that

$$\Gamma, x : (\mu \mid A), \Delta, \widehat{\bullet}_{\xi} \vdash N : A \circledcirc a$$

By the IH, we have that

$$\Gamma, \Delta, \widehat{\bullet}_{\xi} \vdash N[\Gamma; M/x] : A \circledcirc a$$

and hence by **MOD**

$$\Gamma, \Delta \vdash \text{mod}_{\xi}(N[\Gamma; M/x]) : \langle \xi \mid A \rangle \circledcirc b$$

But this is exactly the definiens of $\text{mod}_{\xi}(N)[\Gamma; M/x]$.

25