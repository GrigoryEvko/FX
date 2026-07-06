Relative Elegance and Cartesian Cubes with One Connection

23

$g$ against $f$ via the usual argument that right maps of a weak factorization system are closed under base change.

**Theorem 3.31** Let $\mathbf{M}$ be a cylindrical premodel category in which

- (D) all objects are cofibrant;
- (E) the fibration extension property is satisfied.

Then the premodel structure on $\mathbf{M}$ defines a model structure.

**Proof** By Theorem 3.23. Condition C is satisfied by Lemma 3.28. Trivial cofibrations have left cancellation by Lemma 3.30, while trivial fibrations have right cancellation by Lemma 3.27.

The fibration extension property can in particular be obtained from the existence of fibrant classifiers for fibrations, i.e., fibrant universes of fibrations. We do not generally expect to have a single classifier for all fibrations, only those below a certain size. Thus we now consider a setup where a premodel category sits inside a larger category containing classifiers for its fibrations.

**Lemma 3.32** Let $\mathbf{E}$ be a category, and let $\mathbf{M}$ be a subcategory of $\mathbf{E}$ equipped with a premodel structure. Say that a map in $\mathbf{E}$ is a fibration if it has the right lifting property against all trivial cofibrations in $\mathbf{M}$. Suppose we have a class $\mathcal{U} \subseteq \mathbf{E}^{\rightarrow}$ of fibrations between fibrant objects that classifies fibrations in $\mathbf{M}$, in following sense:

- (a) every fibration in $\mathbf{M}$ is a pullback of some fibration in $\mathcal{U}$;
- (b) if $p: E \to U$ is a map in $\mathcal{U}$ and $y: X \to U$ is a map with $X \in \mathbf{M}$, then there exists a map in $\mathbf{M}$ which is the pullback of $p$ along $y$:

$$\begin{array}{c} \bullet \longrightarrow E \\ \mathbf{M} \ni \downarrow \quad \downarrow p \\ X \xrightarrow{y} U. \end{array}$$

Then $\mathbf{M}$ has the fibration extension property.

**Proof** Let a fibration $f: Y \to X$ in $\mathbf{M}$ and trivial cofibration $m: X \mapsto X'$ in $\mathbf{M}$ be given. Then $f$ is the pullback of some fibration between fibrant objects $p: E \to U$ in $\mathbf{E}$ along some map $y: X \to U$. As $U$ is fibrant, $y$ extends along $m$ to some $y': X' \to U$. By assumption, we can choose a pullback $f': Y' \to X'$ of $p$ along $y'$ belonging to $\mathbf{M}$. By the pasting law for pullbacks, $f$ is the pullback of $f'$ along $m$.

**Corollary 3.33** Let $\mathbf{E}$ be a category, and let $\mathbf{M}$ be a subcategory of $\mathbf{E}$ equipped with a premodel structure. Suppose that $\mathbf{M}$ is cylindrical and the following conditions are satisfied:

- (D) all objects of $\mathbf{M}$ are cofibrant;
- (F) there is a class of fibrations between fibrant objects in $\mathbf{E}$ that classifies fibrations in $\mathbf{M}$ in the sense of Lemma 3.32.

2025/10/16 00:43