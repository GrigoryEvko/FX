Kan operations 133

**Lemma 6.3.2 (Telescope coercion).** Given $\Psi, x : \mathbb{I} \Vdash \Omega = \Omega'$ tel, the following rules are validated.

$$\frac{\Psi \Vdash r, s \in \mathbb{I} \quad \Psi \Vdash \omega = \omega' \in \Omega[r/x]}{\Psi \Vdash \overline{\text{coe}}_{x,\Omega}^{r\rightarrow s}(\omega) = \overline{\text{coe}}_{x,\Omega'}^{r\rightarrow s}(\omega') \in \Omega[s/x]} \quad \frac{\Psi \Vdash r \in \mathbb{I} \quad \Psi \Vdash \omega \in \Omega[r/x]}{\Psi \Vdash \overline{\text{coe}}_{x,\Omega}^{r\rightarrow r}(\omega) = \omega \in \Omega[r/x]}$$

*Proof.* By induction on the length of the telescopes. In the case $\Psi, x : \mathbb{I} \Vdash \cdot = \cdot$ tel, the two rules are immediate, as $\omega = \omega' = \overline{\text{coe}}_{x,\Omega}^{r\rightarrow s}(\omega) = \overline{\text{coe}}_{x,\Omega'}^{r\rightarrow s}(\omega') = \cdot$. Otherwise, we are in the case $\Psi, x : \mathbb{I} \Vdash (\Omega, a : A) = (\Omega', a : A')$ tel where $\Psi, x : \mathbb{I} \Vdash \Omega = \Omega'$ tel and $\Psi, x : \mathbb{I} \Vdash A = A'$ type, so that $\omega = (\chi, M)$ and $\omega' = (\chi', M'/a)$. By induction hypothesis, we know that $\Psi, x : \mathbb{I} \Vdash \overline{\text{coe}}_{x,\Omega}^{r\rightarrow x}(\chi) = \overline{\text{coe}}_{x,\Omega'}^{r\rightarrow x}(\chi') \in \Omega$, so by substituting in $A, A'$ we get $\Psi, x : \mathbb{I} \Vdash A[\overline{\text{coe}}_{x,\Omega}^{r\rightarrow x}(\chi)] = A'[\overline{\text{coe}}_{x,\Omega'}^{r\rightarrow x}(\chi')]$ type. As $A$ and $A'$ are Kan, we may coerce $M$ and $M'$ along these lines, obtaining the following.

$$\Psi \Vdash \text{coe}_{x,A[\overline{\text{coe}}_{x,\Omega}^{r\rightarrow s}(\chi)]}^{r\rightarrow s}(M) = \text{coe}_{x,A'[\overline{\text{coe}}_{x,\Omega'}^{r\rightarrow s}(\chi')]}^{r\rightarrow s}(M') \in A[\overline{\text{coe}}_{x,\Omega}^{r\rightarrow s}(\chi), s/x]$$

Combining this with $\Psi, x : \mathbb{I} \Vdash \overline{\text{coe}}_{x,\Omega}^{r\rightarrow x}(\chi) = \overline{\text{coe}}_{x,\Omega'}^{r\rightarrow x}(\chi') \in \Omega$ and consulting the definition of $\overline{\text{coe}}$, we thus have $\Psi \Vdash \overline{\text{coe}}_{x,\Omega,a:A}^{r\rightarrow s}(\chi, M/a) = \overline{\text{coe}}_{x,\Omega',a:A'}^{r\rightarrow s}(\chi', M'/a) \in (\Omega, a : A)[s/x]$. The second rule follows by a similar argument. $\square$

It will be convenient to have a notion of when an open relation or relation on instantiations supports coercion at some syntactic type.

**Definition 6.3.3.** Given a $\Gamma$-relation $R$, we say that $R$ *supports coercion at* $A, A'$ when $R\gamma$ supports coercion at $A\gamma, A'\gamma'$ for every $\Psi \Vdash \gamma = \gamma' \in \Gamma$.

**Definition 6.3.4.** We say that a $\Psi$-PER $R$ on instantiations *supports coercion at telescopes* $\Omega, \Omega'$ when it validates the following rules for every $\Psi', x : \mathbb{I} \Vdash \psi \in \Psi$ and $\Psi' \Vdash r, s \in \mathbb{I}$.

$$\frac{\omega \approx \omega' \in R\psi[r/x]}{\overline{\text{coe}}_{x,\Omega\psi}^{r\rightarrow s}(\omega) \approx \overline{\text{coe}}_{x,\Omega'\psi}^{r\rightarrow s}(\omega') \in R\psi[s/x]} \quad \frac{\omega \in R\psi[r/x]}{\overline{\text{coe}}_{x,\Omega\psi}^{r\rightarrow r}(\omega) \approx \omega \in R\psi[r/x]}$$

Recall from Section 5.3 that we separate coercion into two parts: the formal coercions between indices of the family—which we have already shown are well-typed—and *parameter coercion*, which coerces along lines $\Psi, x : \mathbb{I} \Vdash \Delta$ tel and $\Psi, x : \mathbb{I} \Vdash \Delta \blacktriangleright \mathcal{K}$ spec in the specification (and thus in the parameters of the type). We intend the parameter coercion operator, pcoe, is intended to satisfy the following rules.