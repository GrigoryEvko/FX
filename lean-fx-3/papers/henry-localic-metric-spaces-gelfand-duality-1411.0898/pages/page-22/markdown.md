6. Assume that $\mathcal{L} \times \mathcal{L} \subseteq \Delta_q$ and $\mathcal{M} \times \mathcal{M} \subseteq \Delta_{q'}$, we will prove that, under the assumption of the proposition, $(\mathcal{L} \vee \mathcal{M}) \times (\mathcal{L} \vee \mathcal{M}) \subseteq \Delta_{q+q'}$.

As $(\mathcal{L} \vee \mathcal{M}) \times (\mathcal{L} \vee \mathcal{M}) = (\mathcal{L} \times \mathcal{L}) \vee (\mathcal{L} \times \mathcal{M}) \vee (\mathcal{L} \times \mathcal{M}) \vee (\mathcal{M} \times \mathcal{M})$ and $(\mathcal{L} \times \mathcal{L})$ and $(\mathcal{M} \times \mathcal{M})$ are already known to be subsets of $\Delta_{q+q'}$, we only have to prove it for $(\mathcal{L} \times \mathcal{M})$ and $(\mathcal{M} \times \mathcal{L})$. In $X^3$ one has:

$$\begin{array}{rcl} \mathcal{M} \times (\mathcal{L} \wedge \mathcal{M}) \times \mathcal{L} & \subseteq & \pi_{1,2}^*(\mathcal{M} \times \mathcal{M}) \wedge \pi_{2,3}^*(\mathcal{L} \times \mathcal{L}) \quad \subseteq \quad \pi_{1,2}^*(\Delta_q') \wedge \pi_{2,3}^*(\Delta_q) \\ & & \subseteq \pi_{1,3}^*(\Delta_{q'+q}) \end{array}$$

Applying $(\pi_{1,3})_!$ yields the result because as $(\mathcal{L} \times \mathcal{M})$ contains some positive and locally positive sublocale, the projection $\pi_{1,3}$ from $\mathcal{L} \times (\mathcal{L} \wedge \mathcal{M}) \times \mathcal{M}$ to $\mathcal{L} \times \mathcal{M}$ is a surjection.

7. It is immediate by induction on $n$ using the previous point.

8. Thanks to the point 2, it is enough to check that $\mathcal{O}(X)^{<q}$ covers $X$. Take a covering of $\Delta_{q/2}$ by open sublocales of the form $U_i \times V_i$, then pulling back along the diagonal embeddings of $X$ into $\Delta_{q/2}$ one has:

$$X = \bigvee_i U_i \wedge V_i$$

but $(U_i \wedge V_i)^2 \leqslant U_i \times V_i \leqslant \Delta_{q/2}$ hence $\delta(U_i \wedge V_i) < q$ which concludes the proof.

9. Thanks to the previous point, for any $q' < q$, $\Delta_{q'}$ can be written as a union of $U_i \times V_i$ with $\delta(U_i) < q'$ and $\delta(V_i) < q'$. If $U_i \times V_i \subseteq \Delta_{q'}$, then so does $V_i \times U_i$, and hence, in our situation:

$$(U_i \cup V_i)^2 = (U_i \times U_i) \cup (V_i \times U_i) \cup (U_i \times V_i) \cup (V_i \times V_i) \subseteq \Delta_{q'}$$

Hence $\delta(U_i \cup V_i) < q$ and the $(U_i \cup V_i)^2$ cover $\Delta_{q'}$. This being done for an arbitrary $q' < q$, these open sublocales also cover $\Delta_q$, because as the $\Delta_q$ are defined by a function from $X \times X$ to $\overleftarrow{\mathbb{R}}^\infty$ one has

$$\Delta_q = \bigvee_{q' < q} \Delta_{q'}$$

10. Applying the definition of $B_q V$ using that $\pi_1^*(\mathcal{L}) = \mathcal{L} \times X$ and the previous point gives directly

$$B_q \mathcal{L} = (\pi_2)_! \left( \bigvee_{\delta(U) < q} (\mathcal{L} \wedge U) \times U \right) = \bigvee_{\substack{\delta(U) < q \\ \mathcal{L} \wedge U > \emptyset}} U.$$

11. From the previous point

$$B_q(B_{q'} \mathcal{L}) = \bigvee_{\substack{v \in \mathcal{O}(X) < q \\ v \wedge B_{q'} \mathcal{L} > \emptyset}} v$$

22