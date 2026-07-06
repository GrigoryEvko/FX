3.1.3. We will denote by $\mathcal{O}(X)^{<q}$ the set of open sublocales $U$ of $X$ such that $\delta(U) < q$, and $\mathcal{O}(X)^{+,<q}$ will be simply the subset $\mathcal{O}(X)^+ \cap \mathcal{O}(X)^{<q}$ of positive elements of $\mathcal{O}(X)^{<q}$.

# 3.1.4. Proposition :

1. $B_q \mathcal{L} \subseteq \mathcal{M}$ if and only if $\mathcal{L} \triangleleft_q \mathcal{M}$.

2. If $\mathcal{L} \subseteq \mathcal{M}$ then $\delta(\mathcal{L}) \leqslant \delta(\mathcal{M})$.

3. If $\mathcal{L} \triangleleft \mathcal{M}$ then $\mathcal{L} \subseteq \mathcal{M}$. In particular for all positive rational numbers $q$ one has $\mathcal{L} \subseteq B_q \mathcal{L}$.

4. If $\mathcal{L} \triangleleft_q \mathcal{M}$ and $\mathcal{L}' \triangleleft_q \mathcal{M}'$ then $\mathcal{L} \wedge \mathcal{L}' \triangleleft_q \mathcal{M} \wedge \mathcal{M}'$ and $\mathcal{L} \vee \mathcal{L}' \triangleleft_q \mathcal{M} \vee \mathcal{M}'$.

5. $\delta\left(\bigvee_{i \in I} \mathcal{L}_i\right) = \sup_{i,j \in I} \delta(\mathcal{L}_i \vee \mathcal{L}_j)$

6. If $\mathcal{L} \wedge \mathcal{M}$ contains a positive and locally positive sublocale then $\delta(\mathcal{L} \vee \mathcal{M}) \leqslant \delta(\mathcal{L}) + \delta(\mathcal{M})$.

7. Let $(\mathcal{L}_i)_{i=0 \dots n}$ be a finite sequence of sublocales such that for all $i$, $\mathcal{L}_{i-1} \wedge \mathcal{L}_i$ contains a positive and locally positive sublocale then:

$$\delta\left(\bigvee_{i=0}^n \mathcal{L}_i\right) \leqslant \sum_{i=0}^n \delta(\mathcal{L}_i)$$

8. For any $q > 0$, $\mathcal{O}(X)^{<q}$ is a basis of the topology of $X$.

9. $\Delta_q = \bigvee_{U \in \mathcal{O}(X)^{<q}} U \times U$

10. If $\mathcal{L}$ is locally positive, then

$$B_q \mathcal{L} = \bigvee_{\substack{U \in \mathcal{O}(X)^{<q} \\ U \wedge \mathcal{L} > \emptyset}} U.$$

In particular, if $\mathcal{L}$ is locally positive, $B_q \mathcal{L}$ is open.

11. If $\mathcal{L}$ is locally positive then

$$B_{q'}(B_q(\mathcal{L})) \subseteq B_{q+q'}(\mathcal{L}).$$

12. If $\mathcal{L}$ is locally positive then $\delta(B_q \mathcal{L}) \leqslant 2q + \delta(\mathcal{L})$.

# Proof :

1. This is simply the adjunction between $(\pi_2)_!$ and $(\pi_2)^*$.

20