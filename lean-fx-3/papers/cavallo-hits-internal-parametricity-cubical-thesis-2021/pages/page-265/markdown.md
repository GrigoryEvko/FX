Rules for modal operators and hypotheses 253

*Proof.* We have $\Gamma, (\mu \mid a : A).\mu = \Gamma.\mu, (\mu \div \mu \mid a : A)$ by Lemma 14.3.14. Note that we have $\Gamma.\mu, (\mu \div \mu \mid a : A) \gg A$ pretype $\otimes m$ by weakening, which is an immediate consequence of the definitions of the open judgments. Let a closing substitution $\Psi \Vdash (\gamma, M/a) = (\gamma', M'/a) \in (\Gamma.\mu, (\mu \div \mu \mid a : A)) \otimes m$ be given; we have $\Psi \Vdash \gamma = \gamma' \in \Gamma.\mu \otimes m$ and $\Psi.(\mu \div \mu) \Vdash M = M' \in A\gamma \otimes m$. Using that $\mu \div \mu$ does not contain glo, we can see that $\Psi \Vdash \text{id}_\Psi \in \Psi.(\mu \div \mu) \otimes m$. By stability of the element judgment, we thus have $\Psi \Vdash M = M' \in A\gamma \otimes m$ as needed. $\square$

# **Corollary 14.3.16 (Action of modal hypotheses).**

$$\frac{\Gamma', \Gamma \text{ ctx } \otimes n \quad \Gamma' \gg \gamma = \gamma' \in \Gamma \otimes n \quad \mu : m \rightarrow n \quad \Gamma.\mu \gg A \text{ pretype } \otimes m}{\Gamma', (\mu \mid a : A\gamma) \gg (\gamma, a/a) = (\gamma', a/a) \in \Gamma, (\mu \mid a : A) \otimes n}$$

*Proof.* By the substitution formation rule and variable rule. $\square$

# **Corollary 14.3.17 (Identity substitution).**

$$\frac{\Gamma = \Gamma' \text{ ctx } \otimes m}{\Gamma \gg \text{id}_\Gamma = \text{id}_{\Gamma'} \in \Gamma \otimes m}$$

*Proof.* By induction on $\Gamma = \Gamma' \text{ ctx } \otimes m$, using the action of each context constructor. $\square$

The remaining properties of the open judgments now require little ingenuity to verify, being for the most part a rehash of the corresponding properties of extended closing substitutions. We leave the construction of detailed proofs as an exercise to the reader.

**Proposition 14.3.18 (Instantiation of substitutions).** If $\Psi \Vdash \delta = \delta' \in \Gamma' \otimes m$ and $\Gamma' \gg \gamma = \gamma' \in \Gamma \otimes m$, then $\Psi \Vdash \gamma\delta = \gamma'\delta' \in \Gamma \otimes m$.

*Proof.* By induction on the derivation of $\Gamma' \gg \gamma = \gamma' \in \Gamma \otimes m$. In the case of a modal hypothesis, we use the functorial action of modalities on extended closing substitutions. $\square$

**Corollary 14.3.19 (Stability of open typing judgments).** Given $\Gamma' \gg \gamma = \gamma' \in \Gamma \otimes m$ and $\Gamma \gg A = A'$ pretype $\otimes m$, we have $\Gamma' \gg A\gamma = A'\gamma'$ pretype $\otimes m$; likewise for types and terms.

# **Proposition 14.3.20 (Action by modalities).**

$$\frac{\Gamma' \gg \gamma = \gamma' \in \Gamma \otimes n \quad \mu : m \rightarrow n}{\Gamma'.\mu \gg (\gamma : \Gamma) \otimes \mu = (\gamma' : \Gamma) \otimes \mu \in \Gamma.\mu \otimes m}$$

*Proof.* Following the proof of Corollary 14.3.6, now using Lemma 14.3.12. $\square$