**2.6.3. Proposition :** If $X$ is compact completely regular and $B$ is an admissible basic sublocale of $[X, \mathbb{R}]$, then $B$ has a point. If $X$ is just compact regular and $B$ is admissible then $B$ is positive.

**Proof :**

Assume that $X$ is completely regular, and let us first remark that when $X$ is a compact completely regular locale, if $U$ and $V$ are two open sublocales of $X$ such that $(\neg U) \vee (\neg V) = X$, then, as $U \ll (\neg V)$, it is possible to construct a continuous function $f : X \rightarrow [0, 1]$ such that $f$ restricted to $U$ is constant equal to 0 and $f$ restricted to $V \subseteq \neg \neg V$ is constant equal to 1.

Now let

$$B = \left( \bigwedge_{i=1}^n (U_i, u_i, -) \right) \wedge \left( \bigwedge_{j=1}^m (V_j, v_j, +) \right)$$

be an admissible basic sublocale of $[X, \mathbb{R}]$.

Let $\epsilon$ be a positive rational number smaller than all the positive differences between two numbers of the form $u_i$ or $v_i$. For each couple $(i, j)$ we choose a continuous function $f_{i,j} : X \rightarrow \mathbb{R}$ such that:

- If $v_j < u_i$ then $f_{i,j}$ is the constant function equal to $\frac{v_j \leq u_i}{2}$
- If $u_i \leq v_j$ then $(\neg U_i) \vee (\neg V_j) = X$ and $f_{i,j}$ is a continuous function such that $f$ is constant equal to $u_i - \epsilon$ on $U_i$, $f$ is constant equal to $v_j + \epsilon$ on $V_j$ and $f$ takes value in $[u_i - \epsilon, v_j + \epsilon]$. (such a function exists by the previous remark).

Then,

$$f = \max_{1 \leq j \leq m} \min_{1 \leq i \leq n} f_{i,j},$$

is a point of $B$. Indeed:

- Let $i \in \{1, \dots, n\}$, then (on $U_i$), since for each $j$, $f_{i,j}$ is smaller than $u_i - \frac{\epsilon}{2}$, the infimum $\inf_{i'=1}^n f_{i',j}$ is smaller than $u_i - \frac{\epsilon}{2}$ and $f$ smaller than $u_i - \frac{\epsilon}{2}$ on $U_i$ as a (finite) supremum of a quantities smaller than $u_i - \frac{\epsilon}{2}$.
- Let $j \in \{1, \dots, m\}$, then (on $V_j$), as for each $i$, $f_{i,j}$ is greater than $v_j + \frac{\epsilon}{2}$, the infimum $\inf_{i=1}^n f_{i,j}$ is greater than $v_j + \frac{\epsilon}{2}$. And $f$ is greater than $v_j + \frac{\epsilon}{2}$ on $V_j$.

This concludes the proof when $X$ is completely regular. We now assume that $X$ is only regular. Then all the functions $f_{i,j}$ we used in the first part can be instead constructed in the logic of positive locally positive locales $\mathcal{L}_{i,j}$ using 2.6.2. The product $\mathcal{L}$ of all these $\mathcal{L}_{i,j}$ is also positive and locally positive by 2.3.7, and in the logic of $\mathcal{L}$, all the functions $f_{i,j}$ we used in the first part exist and hence one can construct the function $f$ which is going to be a point of $B$ in the logic of $\mathcal{L}$ exactly as we did above. This defines a map $\mathcal{L} \rightarrow B$ and, as $\mathcal{L}$ is positive, this proves that $B$ is positive and concludes the proof. $\square$

16