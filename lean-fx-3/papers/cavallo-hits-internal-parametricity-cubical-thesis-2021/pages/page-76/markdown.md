64

Cubical type theory

Lemma 3.1.34 (Coherent value introduction). Let $R$ be a value $\Psi$-relation, and let $M$ and $M'$ be terms in context $\Psi$. If for all $\Psi' \Vdash \psi \in \Psi$, either $M\psi \approx M'\psi \in R\psi$ or $M\psi \approx M'\psi \in \Downarrow R\psi$, then $M \approx M' \in \Downarrow R$.

Proof. Let $\Psi_1 \Vdash \psi_1 \in \Psi$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$ be given. We are in one of two cases.

- $M\psi_1 \approx M'\psi_1 \in \Downarrow R\psi_1$.

Instantiating this relation with the substitutions $\Psi_1 \Vdash \mathrm{id}_{\Psi_1} \in \Psi_1$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$, we get that $M\psi_1 \Downarrow V$ and $M'\psi_1 \Downarrow V'$ with $N \approx N' \in \Downarrow R\psi\psi_1\psi_2$ for $N \in \{M\psi_1\psi_2, V\psi_2\}$ and $N' \in \{M'\psi_1\psi_2, V'\psi_2\}$, as needed.

- $M\psi_1 \approx M'\psi_1 \in R\psi_1$.

Then $M\psi_1$ and $M'\psi_1$ are values, so the requirement reduces to showing that $M\psi_1\psi_2 \approx M'\psi_1\psi_2 \in \Downarrow R\psi\psi_1\psi_2$. This is the case both if $M\psi_1\psi_2 \approx M'\psi_1\psi_2 \in R\psi_1\psi_2$ and if $M\psi_1\psi_2 \approx M'\psi_1\psi_2 \in \Downarrow R\psi_1\psi_2$. $\square$

Second, we have an analogue of head expansion. Given a term $M'$ in $R$, it is not necessarily the case that any $M$ such that $M \longmapsto M'$ is equal to $M'$ in $R$. If, however, every instance $M\psi$ steps to a term equal to $M'\psi$, then we can deduce an equality.

Lemma 3.1.35 (Coherent head expansion). Let $R$ be a value $\Psi$-PER, and let $M, M'$ be terms in context $\Psi$. If for every $\Psi' \Vdash \psi \in \Psi$, we have $M\psi \longmapsto^* M_\psi$ for some $M_\psi$ with $M_\psi \approx M'\psi \in \Downarrow R\psi$, then $M \approx M' \in \Downarrow R$.

Proof. Let $\Psi_1 \Vdash \psi_1 \in \Psi$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$ be given. First, we have some $M_1$ with $M\psi_1 \longmapsto^* M_1$ and $M_{\psi_1} \approx M'\psi \in \Downarrow R\psi_1$. By instantiating the latter fact at the substitutions $\Psi_1 \Vdash \mathrm{id}_{\Psi_1} \in \Psi_1$ and $\Psi_2 \Vdash \psi_2 \in \Psi_1$, we have some $V$ and $V'$ such that $M\psi_1 \longmapsto^* M_1 \Downarrow V$, $M\psi_2 \Downarrow V'$, and $N \approx N' \in \Downarrow R\psi\psi_1\psi_2$ for $N \in \{M_1\psi_2, V\psi_2\}$ and $N' \in \{M'\psi_1\psi_2, V'\psi_2\}$.

Second, we have some $M_2$ with $M\psi_1\psi_2 \longmapsto^* M_2$ and $M_2 \approx M'\psi_1\psi_2 \in \Downarrow R\psi_1\psi_2$. This implies in particular that $M\psi_1\psi_2 \approx M'\psi_1\psi_2 \in \Downarrow R\psi_1\psi_2$. Finally, by the assumption that $R$ is a PER, we can deduce the final necessary relation, $M\psi_1\psi_2 \approx V'\psi_2 \in \Downarrow R\psi_1\psi_2$, from the other three. $\square$

Once we can establish that $\Psi$-PER $R$ is value-coherent—something we usually use the above lemmas to prove—we can deduce that terms in $\Downarrow R$ are related to their values.

Lemma 3.1.36 (Evaluation). Let $R$ be a value-coherent value $\Psi$-PER and let $M \in \Downarrow R$. Then $M \Downarrow V$ with $M \approx V \in \Downarrow R$.

Proof. Instantiating $M \in \Downarrow R$ with identity substitutions, we know that $M \Downarrow V$. Moreover, for any $\Psi' \Vdash \psi \in \Psi$, instantiating $M \in \Downarrow R$ with $\mathrm{id}_{\Psi}$ and $\psi$ tells us in particular that