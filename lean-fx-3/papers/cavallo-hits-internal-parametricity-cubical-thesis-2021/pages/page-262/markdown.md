250

Cohesive parametric type theory

property we need, is the one we are really after; the others represent a strengthening of induction hypothesis.

Lemma 14.3.10. Let $\mu : m \to n$. Then the following hold.

(1) If $n = \text{par}$ and $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{glo.dsc.}\mu \circledast m$, then there exist $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\mu \circledast m$.
(2) If $n = \text{par}$ and $\Psi \Vdash \gamma = \gamma' \in \Gamma.\mu \circledast m$, then there exist $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\text{cc.dsc.}\mu \circledast m$.
(3) If $n = \text{pt}$ and $\Psi \Vdash \gamma = \gamma' \in \Gamma.\mu \circledast m$, then there exist $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\text{dsc.glo.}\mu \circledast m$.
(4) If $n = \text{pt}$ and $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{dsc.glo.}\mu \circledast m$, then there exist $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\mu \circledast m$.
(5) If $n = \text{pt}$ and $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{glo.}\mu \circledast m$, then there exist $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\text{cc.}\mu \circledast m$.

Moreover, in each case, we have $M\gamma_+ = M\gamma$ and $M\gamma'_+ = M\gamma'$ for any term $M$, up to syntactic equality.

Proof. By induction on the length of $\mu$, proving all of the above simultaneously as follows.

(1) By cases on $\mu$.
- $\mu = \text{id}$. Then by the adjunctions on closing substitutions, we have $\Psi.\text{dsc.cc} \gg \gamma = \gamma' \in \Gamma \circledast \text{par}$, and we have $\Psi.\text{dsc.cc} = \Psi$.
- $\mu = (\text{cc}, \mu')$. Then we are given $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{glo.dsc.cc.}\mu' \circledast m$. As $-\text{cc}$ cancels $-\text{dsc}$, this means we have $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{glo.}\mu' \circledast m$. It follows from (5) applied with $\mu'$ that we have some $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\mu \circledast m$.
- $\mu = (\text{glo}, \mu')$. Then we are given $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{glo.dsc.glo.}\mu' \circledast m$. It follows from (4) applied with $\mu'$ that we have some $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\mu \circledast m$.
(2) By cases on $\mu$.
- $\mu = \text{id}$. Then by the action of cc on closing substitutions we have some $\Psi.\text{cc} \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\text{cc} \circledast \text{pt}$, and it follows by the components-discrete adjunction that $\Psi \Vdash \gamma_+ = \gamma'_+ \in \Gamma.\text{cc.dsc} \circledast \text{par}$.
- $\mu = (\text{cc}, \mu')$. Then we are given $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{cc.}\mu' \circledast m$, and it follows that $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{cc.dsc.cc.}\mu' \circledast m$ because $-\text{cc}$ cancels $-\text{dsc}$ (up to syntactic equality).
- $\mu = (\text{glo}, \mu')$. Then we are given $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{glo.}\mu' \circledast m$. It follows from (5) applied with $\mu'$ that $\Psi \Vdash \gamma = \gamma' \in \Gamma.\text{cc.}\mu' \circledast m$, and then we proceed as in the previous case.
(3) By cases on $\mu$.