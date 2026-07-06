3.6.3. **Theorem :** *There is an equivalence of categories between the category of weakly spatial complete metric locales (with metric maps) and complete metric sets (with metric maps).*

# **Proof :**

The functors are given by the following construction: to a complete metric set $X$ one associates its localic completion $\tilde{X}$, which is weakly spatial, because $X$ is fiberwise dense in it, and to a weakly spatial complete metric locale one associates its set of points endowed with the induced distance. These two constructions are functorial on metric maps.

By definition of a complete metric set it identifies with the set of points of its localic completion, and conversely, if $\mathcal{L}$ is a weakly spatial complete metric locale and $X$ is its set of points endowed with the induced distance, then $X \rightarrow \mathcal{L}$ is a fiberwise dense isometric map from $X$ to a complete locale, hence $\mathcal{L}$ is isomorphic to the completion of $X$. This proves that the two functors are inverse from each other on objects. They are also inverse of each other on morphisms, tautologically on one side and by 3.2.3 on the other side. $\square$

3.6.4. The internal application of the fact that the set of points of a complete metric locale is complete in the classical sense can prove directly a result of completeness of the space of functions with values in a complete locale for the uniform distance. This cannot be stated directly in terms of completeness of some metric locale because in general (if the initial space is not locally compact) the space of functions is not a locale, but one has:

**Proposition :** *Let $(f_i)_{i \in I}$ be a Cauchy net of functions between two locales $X$ and $Y$, with $Y$ a complete metric locale. This means that $I$ is a directed (filtering) ordered set and that for all positive rational number $\epsilon$ there exists $i_0 \in I$ such that $\forall i, j \geq i_0$, the map $(f_i, f_j)$ factors into $\Delta_\epsilon \subset Y \times Y$.*

*Then the net $f_i$ converges to some (uniquely defined) function $f : X \rightarrow Y$. This mean that there is a unique function $f : X \rightarrow Y$ such that for all positive rational number $\epsilon$ there exists $i_0 \in I$ such that $\forall i \geq i_0$, the map $(f, f_i)$ factors into $\Delta_\epsilon$.*

# **Proof :**

The net of functions $f_i : X \rightarrow Y$ can be interpreted as a net of points of $p^\#Y$ in the logic of $X$ (where $p$ is the map $X \rightarrow *$). And the fact that it is externally a Cauchy net immediately gives that it is internally a Cauchy net. The usual proof that completeness by filter imply completeness by net is completely constructive$^{10}$ and hence the fact that $p^\#Y$ is complete implies the convergence of the net $f_i$. Uniqueness of the limit implies that the limit is a global point of $p^\#Y$ in $X$, and hence a map from $X$ to $Y$. One then easily check that the internal convergence together with the external Cauchy condition imply the external convergence. $\square$

$^{10}$On the contrary, the converse relies on the axiom of choice.

49