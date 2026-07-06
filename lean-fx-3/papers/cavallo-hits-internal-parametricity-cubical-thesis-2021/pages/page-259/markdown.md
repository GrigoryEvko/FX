Rules for modal operators and hypotheses 247

**Corollary 14.3.3 (Extended instantiation).** Given any $\Upsilon \gg \gamma = \gamma' \in \Gamma \otimes m$ and any $\Gamma \gg A = A'$ pretype $\otimes m$, we have $\Upsilon \gg A\gamma = A'\gamma'$ pretype $\otimes m$; likewise for types and terms.

In order to avoid repetition, we introduce the following notion of modality *division*, following Nuyts, Vezzosi, and Devriese [NVD17].

**Definition 14.3.4 (Division).** We define $\mu \div \nu : m \to n$ as a partial function of $\mu : m \to p$ and $\nu : n \to p$ as follows.

$$\begin{aligned} \mu \div \text{id} &:= \mu \\ (\text{cc}, \mu) \div (\text{cc}, \nu) &:= \mu \div \nu \\ \mu \div (\text{dsc}, \nu) &:= (\text{cc}, \mu) \div \nu \\ \mu \div (\text{glo}, \nu) &:= (\text{dsc}, \mu) \div \nu \end{aligned}$$

This expresses compactly the effect of context operators on modal hypotheses, as shown by the following equations.

$$\begin{aligned} \Gamma, (\mu \mid a : A).\nu &= \Gamma.\nu, (\mu \div \nu \mid a : A) && \text{if } \mu \div \nu \text{ is defined} \\ \Gamma, (\mu \mid a : A).\nu &= \Gamma.\nu && \text{otherwise} \end{aligned}$$

The following lemma is key; it tells us that modal hypotheses remain well-typed after the application of a modality.

**Lemma 14.3.5 (Division of extended closed terms).** Let $\mu : m \to p$ and $\nu : n \to p$. If $\Upsilon.\mu \gg M = M' \in A \otimes m$ and $\mu \div \nu$ is defined, then $\Upsilon.\nu.(\mu \div \nu) \gg M = M' \in A \otimes m$.

*Proof.* By induction on $\nu$.

- Case: $\nu = \text{id}$. Immediate.
- Case: $\nu = (\text{cc}, \nu')$. Then we must have $\mu = (\text{cc}, \mu')$, and the result follows by induction hypothesis applied with $\nu'$ and $\mu'$.
- Case: $\nu = (\text{dsc}, \nu')$. We have $\Upsilon = \Upsilon.\text{dsc.cc}$, so we can apply the induction hypothesis with $\nu'$ and $(\text{cc}, \mu)$ at $\Upsilon.\text{dsc.cc.}\mu \gg M = M' \in A \otimes m$ to get the result.
- Case: $\nu = (\text{glo}, \nu')$. We have a substitution $\Upsilon.\text{glo.dsc.}\mu \gg \text{id}_{\Upsilon.\mu} \in \Upsilon.\mu$ by the action of modalities on and adjunction laws for extended interval substitutions. It follows by stability that $\Upsilon.\text{glo.dsc.}\mu \gg M = M' \in A \otimes m$. Applying the induction hypothesis with $\nu'$ and $(\text{dsc}, \mu)$ gives the result. $\square$