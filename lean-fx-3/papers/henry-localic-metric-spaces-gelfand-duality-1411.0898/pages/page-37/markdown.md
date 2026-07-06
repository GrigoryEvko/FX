Consider an arbitrary Cauchy filter $F$ on $X$ such that $V \in F$. Then there exists $V' \triangleleft V$ such that $V' \in F$ and hence $U \in F$. This proves that $V^{\sim} \leqslant U^{\sim}$ and hence, as $V^{\sim} \leqslant U^{\sim}$ imply $V^{\sim} \leqslant i_{\star}(U)$ one has $V^{\sim} \leqslant i_{\star}U$ if and only if $V^{\sim} \leqslant U^{\sim}$ hence as the $V^{\sim}$ form a basis of $\widetilde{X}$ this proves that $i_{\star}(U) = U^{\sim}$.

**3.3.9. Proposition :** *The canonical map $i: X \rightarrow \widetilde{X}$ is fiberwise dense and $\widetilde{X}$ is locally positive.*

**Proof :**

The $(B_q V)^{\sim}$ for $q$ a positive rational number and $V$ a positive element of $\mathcal{O}(X)$ form a basis of $\widetilde{X}$. Indeed, the $U^{\sim}$ for $U \in \mathcal{O}(X)^+$ form a basis, and for any $U \in \mathcal{O}(X)$ by (CF4),

$$U^{\sim} = \bigvee_{\substack{V \triangleleft U \\ V > \delta}} V^{\sim} = \bigvee_{B_q V \leqslant U} (B_q V)^{\sim}.$$

Moreover,

$$i^*((B_q V)^{\sim}) = \bigvee_{U \triangleleft B_q V} U \geqslant \bigvee_{q' < q} B_{q'} V = B_q V.$$

Hence one has a basis of elements of $\widetilde{X}$ whose pre-image by $i$ are positive. This implies that $\widetilde{X}$ has a basis of positive elements and that for each positive element of $\widetilde{X}$ its pre-image along $i$ is positive, which concludes the proof. $\square$

**3.3.10. Proposition :** *There is a distance function $d$ on $\widetilde{X}$ such that*

$$\Delta_q = \bigvee_{U \in \mathcal{O}(X)^{<q}} U^{\sim} \times U^{\sim}.$$

One might note that this definition of the distance on $\widetilde{X}$ is the point-free formulation of the more usual definition:

$$d(\mathcal{F}, \mathcal{F}') < q \text{ if and only if } \exists u \in \mathcal{F} \wedge \mathcal{F}' \text{ with } \delta(u) < q$$

which is equivalent if interpreted in terms of generalized points.

**Proof :**

Let $U \in \mathcal{O}(X)$ such that $\delta(U) < q$. Then there exists $q'$ such that $\delta(U) < q'$ and $U^{\sim} \times U^{\sim} \leqslant \Delta_{q'}$. Hence

$$\Delta_q = \bigvee_{q' < q} \Delta_{q'},$$

37