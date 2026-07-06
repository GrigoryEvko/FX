This proves one half of the claim that $(\mu \mid \varphi)$ and $\langle \mu \mid \varphi \rangle$ are equivalent. The other half cannot be shown as a theorem, as an implication cannot have $(\mu \mid \varphi)$ as a conclusion. However, the special case of the modal elimination rule for $\nu \stackrel{\text{def}}{=} 1$

$$\frac{\mu : n \rightarrow m \quad \Gamma \vdash \langle \mu \mid \varphi \rangle \circledcirc m \quad \Gamma, (\mu \mid \varphi) \vdash \psi \circledcirc m}{\Gamma \vdash \psi \circledcirc m}$$

(which follows because $\Gamma, \widehat{\bullet}_1 = \Gamma$ by Eq. (1)) shows how we can 'promote' a modal formula $\langle \mu \mid \varphi \rangle$ and use it as an assumption $(\mu \mid \varphi)$ in the context of another proof. This can be thought as a converse to above proof.

One can also show a version of the $\mathbf{K}$ axiom $\Box(\varphi \rightarrow \psi) \rightarrow \Box\varphi \rightarrow \Box\psi$, where the $\Box$ in the conclusion is replaced by a $\langle \mu \mid -\rangle$, and the two antecedents are tagged:

$$\frac{\frac{1_\mu : \mu \Rightarrow \mu}{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi), \widehat{\bullet}_\mu \vdash \varphi \rightarrow \psi \circledcirc m} \quad \frac{1_\mu : \mu \Rightarrow \mu}{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi), \widehat{\bullet}_\mu \vdash \psi \circledcirc m}}{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi), \widehat{\bullet}_\mu \vdash \psi \circledcirc m} \\ \frac{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi) \vdash \langle \mu \mid \psi \rangle \circledcirc m}{(\mu \mid \varphi \rightarrow \psi), (\mu \mid \varphi) \vdash \langle \mu \mid \psi \rangle \circledcirc m}$$

Consequently all the modalities in our system are necessity-type modalities.

It is interesting to ask how one can handle this type of reasoning *without* using modal antecedents in implications, i.e. replacing antecedents $(\mu \mid \varphi)$ with antecedents $(1 \mid \langle \mu \mid \varphi \rangle)$ with a trivial modal tag and a modal formula. Navigating the difference between $(\mu \mid \varphi)$ and $\langle \mu \mid \varphi \rangle$ is the domain of the modal elimination rule. For example, we can prove that we can eliminate conjunctions under modalities. Given $\varphi, \psi$ wff $\circledcirc n$ and writing $\Gamma \stackrel{\text{def}}{=} (1 \mid \langle \mu \mid \varphi \wedge \psi \rangle), (\mu \mid \varphi \wedge \psi)$ we have

$$\frac{\frac{1_{1_m} : 1_m \Rightarrow 1_m}{(1 \mid \langle \mu \mid \varphi \wedge \psi \rangle) \vdash \langle \mu \mid \varphi \wedge \psi \rangle \circledcirc m} \quad \frac{\frac{1_\mu : \mu \Rightarrow \mu}{\Gamma, \widehat{\bullet}_\mu \vdash \varphi \wedge \psi \circledcirc n}}{\Gamma, \widehat{\bullet}_\mu \vdash \varphi \circledcirc n}}{(1 \mid \langle \mu \mid \varphi \wedge \psi \rangle), (\mu \mid \varphi \wedge \psi) \vdash \langle \mu \mid \varphi \rangle \circledcirc m}}{(1 \mid \langle \mu \mid \varphi \wedge \psi \rangle) \vdash \langle \mu \mid \varphi \rangle \circledcirc m} \\ \frac{(1 \mid \langle \mu \mid \varphi \wedge \psi \rangle) \vdash \langle \mu \mid \varphi \rangle \circledcirc m}{\vdash \langle \mu \mid \varphi \wedge \psi \rangle \rightarrow \langle \mu \mid \varphi \rangle \circledcirc m}$$

Notice that the modal elimination rule is used to turn the modal formula $\langle \mu \mid \varphi \wedge \psi \rangle$ into an assumption $(\mu \mid \varphi \wedge \psi)$ which overpowers the $\mu$-lock. One can also prove the following theorems in a similar manner:

$$\begin{aligned} &\vdash \langle \mu \mid \varphi \rightarrow \psi \rangle \rightarrow \langle \mu \mid \varphi \rangle \rightarrow \langle \mu \mid \psi \rangle \circledcirc m \\ &\vdash \langle \mu \mid \varphi \wedge \psi \rangle \leftrightarrow \langle \mu \mid \varphi \rangle \wedge \langle \mu \mid \psi \rangle \circledcirc m \end{aligned} \tag{3}$$

Both of these are versions of the $\mathbf{K}$ axiom.

15