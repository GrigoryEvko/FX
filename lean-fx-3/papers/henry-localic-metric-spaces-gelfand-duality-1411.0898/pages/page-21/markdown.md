2. If $\mathcal{L} \subseteq \mathcal{M}$ and if $\delta(\mathcal{M}) < q$ then there exists a positive rational $q' < q$ such that $\mathcal{L} \times \mathcal{L} \subseteq \mathcal{M} \times \mathcal{M} \subseteq \Delta_{q'}$ hence $\delta(\mathcal{L}) < q$.

3. Assume that $\pi_1^*(\mathcal{L}) \wedge \Delta_q \subseteq \pi_2^*(\mathcal{M})$ for some positive rational number $q$, and let $i: X \to X \times X$ be the diagonal embedding, then:

$$i^*(\pi_1^*(\mathcal{L}) \wedge \Delta_q) \subseteq i^*\pi_2^*(\mathcal{M}) = \mathcal{M}$$

And:

$$i^*(\pi_1^*(\mathcal{L}) \wedge \Delta_q) = i^*\pi_1^*(\mathcal{L}) \wedge i^*\Delta_q = \mathcal{L} \wedge X = \mathcal{L}$$

hence $\mathcal{L} \subseteq \mathcal{M}$. The second part of the result then follows from the fact that as $B_q\mathcal{L} \subseteq B_q\mathcal{L}$, one has $\mathcal{L} \triangleleft_q B_q\mathcal{L}$.

4. Assume that $\pi_1^*\mathcal{L} \wedge \Delta_q \subseteq \pi_2^*\mathcal{M}$ and that $\pi_1^*\mathcal{L}' \wedge \Delta_q \subseteq \pi_2^*\mathcal{M}'$, then:

$$\pi_1^*(\mathcal{L} \wedge \mathcal{L}') \wedge \Delta_q = \pi_1^*(\mathcal{L}) \wedge \Delta_q \wedge \pi_1^*(\mathcal{L}') \wedge \Delta_q \subseteq \pi_2^*(\mathcal{M}) \wedge \pi_2^*(\mathcal{M}')$$

hence $\mathcal{L} \wedge \mathcal{L} \triangleleft_q \mathcal{M} \wedge \mathcal{M}$.

And for the union:

$$\begin{array}{rcl} \pi_1^*(\mathcal{L} \vee \mathcal{L}') \wedge \Delta_q & = & (\pi_1^*(\mathcal{L}) \vee \pi_1^*(\mathcal{L}')) \wedge \Delta_q \\ & = & (\pi_1^*\mathcal{L} \wedge \Delta_q) \vee (\pi_1^*\mathcal{L}' \wedge \Delta_q) \\ & \subseteq & \pi_2^*(\mathcal{M}) \vee \pi_2^*(\mathcal{M}'), \end{array}$$

which gives the result.

The fact that intersections distribute over finite unions of sublocales and that pull-backs preserve finite unions of sublocales can be found in [12] C1.1.15 and C.1.19, but formulated in terms of frames instead of locales (i.e. union of sublocales correspond to intersection of nuclei, and pull-back of a sublocale to a pushout).

5. Clearly, $\sup_{i,j \in I} \delta(\mathcal{L}_i \vee \mathcal{L}_j) \leqslant \delta(\bigvee_i \mathcal{L}_i)$ because $\mathcal{L}_i \vee \mathcal{L}_j \subseteq \bigvee_i \mathcal{L}_i$. Let $q$ such that $\sup_{i,j \in I} \delta(\mathcal{L}_i \vee \mathcal{L}_j) < q$ i.e. there exists $q' < q$ such that for all $i, j$, $\delta(\mathcal{L}_i \vee \mathcal{L}_j) < q'$. But as

$$\left( \bigvee_{i \in I} \mathcal{L}_i \right) \times \left( \bigvee_{j \in I} \mathcal{L}_j \right) = \bigvee_{i,j} \mathcal{L}_i \times \mathcal{L}_j$$

and for all $i, j$, $\mathcal{L}_i \times \mathcal{L}_j \subseteq \Delta_{q'}$, one obtains

$$\left( \bigvee_{i \in I} \mathcal{L}_i \right) \times \left( \bigvee_{j \in I} \mathcal{L}_j \right) \subseteq \Delta_{q'},$$

which concludes the proof.

21