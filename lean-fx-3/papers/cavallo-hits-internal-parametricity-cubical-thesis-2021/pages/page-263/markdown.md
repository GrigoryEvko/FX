Rules for modal operators and hypotheses 251

- $\mu = \text{id}$. We have $\Psi = \Psi.\text{dsc.cc}$, so $\Psi.\text{dsc.cc} \Vdash \gamma = \gamma' \in \Gamma \text{ @ pt}$, and then $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{dsc.glo @ pt}$ follows from the components-discrete and discrete-global adjunctions.
- $\mu = (\text{dsc}, \text{id})$. By the components-discrete adjunction, we have $\Psi.\text{cc} \Vdash \gamma = \gamma' \in \Gamma \text{ @ pt}$. By the argument of the previous case, it follows that $\Psi.\text{cc} \Vdash \gamma = \gamma' \in \Gamma.\text{dsc.glo @ pt}$, and then $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{dsc.glo.dsc @ par}$ follows by applying the adjunction in reverse.
- $\mu = (\text{dsc}, \text{cc}, \mu')$. Then as $-.\text{cc}$ cancels $-.\text{dsc}$, this follows by (3) applied with $\mu'$.
- $\mu = (\text{dsc}, \text{glo}, \mu')$. Then this follows by (3) applied with $\mu'$.

(4) By cases on $\mu$.

- $\mu = \text{id}$. Then by the discrete-global and components-discrete adjunctions, it follows that $\Psi.\text{dsc.cc} \Vdash \gamma = \gamma' \in \Gamma \text{ @ pt}$, and we have $\Psi.\text{dsc.cc} = \Psi$.
- $\mu = (\text{dsc}, \mu')$. Then this follows from (1) applied with $\mu'$.

(5) By cases on $\mu$.

- $\mu = \text{id}$. By the discrete-global adjunction we have $\Psi.\text{dsc} \Vdash \gamma = \gamma' \in \Gamma \text{ @ par}$. Then we apply the action of $\text{cc}$ on closing substitutions and the fact that $\Psi.\text{dsc.cc} = \Psi$ to get some $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\text{cc @ pt}$.
- $\mu = (\text{dsc}, \mu')$. Then the result follows by applying first (1) and then (2) with $\mu'$. $\square$

**Lemma 14.3.11.** Let $\mu : m \to n$ and $\nu : p \to m$ be given such that $\mu \div \nu$ is defined. If $\Psi \Vdash \gamma = \gamma' \in \Gamma.\nu.(\mu \div \nu) \text{ @ } m$, then there exist some $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\mu \text{ @ } m$ such that $M\gamma_+ = M\gamma$ and $M\gamma'_+ = M\gamma'$ for any term $M$.

*Proof.* By induction on $\nu$. Suppose $\Psi \Vdash \gamma = \gamma' \in \Gamma.\nu.(\mu \div \nu) \text{ @ } m$; we have four cases.

- $\nu = \text{id}$. Then $\Gamma.\nu.(\mu \div \nu) = \Gamma.\mu$.
- $\nu = (\text{cc}, \nu')$. As we assumed $\mu \div \nu$ is defined, we must have $\mu = (\text{cc}, \mu')$ for some $\mu'$. Then $\Gamma.\nu.(\mu \div \nu) = \Gamma.\text{cc}.\nu'.(\mu' \div \nu')$. The result thus follows by induction hypothesis applied at $\Gamma.\text{cc}, \mu'$, and $\nu'$.
- $\nu = (\text{dsc}, \nu')$. Then $\Gamma.\nu.(\mu \div \nu) = \Gamma.\text{dsc}.\nu'.((\text{cc}, \mu) \div \nu')$. By induction hypothesis applied at $\Gamma.\text{dsc}, \nu'$, and $(\text{cc}, \mu)$, we have some $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\text{dsc.}(\text{cc}, \mu) \text{ @ } m$, and $\Gamma.\text{dsc.cc} = \Gamma$ by inspection.
- $\nu = (\text{glo}, \nu')$. Then $\Gamma.\text{glo}.\nu'.((\text{dsc}, \mu) \div \nu')$. By induction hypothesis applied at $\Gamma.\text{glo}, \nu'$, and $(\text{dsc}, \mu)$, we have some $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\text{glo.}(\text{dsc}, \mu) \text{ @ } m$. By property (1) of **Lemma 14.3.10**, it follows that we have some $\Psi \Vdash \gamma_{++} = \gamma'_{++} \in \Gamma.\mu \text{ @ } m$. $\square$