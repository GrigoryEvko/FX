If $\deg(r) = 0$, then the latching map is just $X(r) \to Y(r)$ itself, so it is a trivial cofibration as it is a cofibration and a weak equivalence. Assume now that we already know that all the latching maps

$$L_r Y \sqcup_{L_r X} X(r) \to Y(r)$$

are trivial cofibrations for any $r$ such that $\deg(r) < \deg(k)$. We can then deduce by the same argument as above that the map $L_k(X) \to L_k(Y)$ is a core trivial cofibration, which shows that the map $X(r) \to L_r Y \sqcup_{L_r X} X(r)$ is a trivial cofibration, hence an equivalence, and hence by 2-out-of-3 for equivalences, the map $L_r Y \sqcup_{L_r X} X(r) \to Y(r)$, is both an equivalence and a core cofibration, so it is a (core) trivial cofibration. $\square$

Note that we have also proved that:

**Lemma C.17.** *Let $R$ be a locally finite Reedy category, and $i : X \to Y$ be a core Reedy cofibration in $\mathcal{M}^R$. Then the domain of the latching map $L_r Y \sqcup_{L_r X} X(r)$ is cofibrant.*

*Proof.* At the beginning of the proof of theorem C.16 we observed that it could be written as a latching object $L_{(r,1)}T$ of a cofibrant Reedy diagram $T$. Hence, the result follows from theorem C.14. $\square$

**Proposition C.18.** *For any locally finite Reedy category $R$, in $\mathcal{M}^R$, the composite of two Reedy core cofibrations is a Reedy core cofibrations.*

*Proof.* We use a strategy very similar to the proof of theorem C.16. Here again, the result only depends on the restriction to $R^+$ so we can freely assume that $R$ is a direct category. Let $X \to Y \to Z$ be two composable Reedy core cofibrations in $\mathcal{M}^R$. We consider this as a diagram $T : R \times \{0 < 1 < 2\} \to \mathcal{M}$. As in the proof of theorem C.16. We observe that the latching map at an element of the form $(r, 0)$ is the latching map $L_r X \to X$ of $X$ hence is a cofibration as $X$ is Reedy cofibrant. The latching map at an element $(r, 1)$ is the map

$$L_r Y \sqcup_{L_r X} X(r) \to Y(r)$$

which is a cofibration as $X \to Y$ is assumed to be a Reedy cofibration. And finally, the latching map at $(r, 2)$ is the map

$$L_r Z \sqcup_{L_r Y} Y(r) \to Z(r)$$

which is also a cofibration. So this diagram $R \times \{0 < 1 < 2\} \to \mathcal{M}$ is Reedy cofibrant. It immediately follows that, for any $r \in R$ the composite

152