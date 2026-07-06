**Example 3.24.** We cannot write the formula

$$\exists x : 0\text{-CW} \forall y : 0\text{-CW}, x = y.$$

The only possibility is to write

$$\forall x, y : 0\text{-CW} \exists \alpha : 1\text{-CW}(x, y), \top$$

which simply says that a space is path-connected. Moreover, we can not say that two paths $\alpha, \beta : 1\text{-CW}(x, x)$ are homotopic in the usual sense, only that there exists $\sigma : 3\text{-CW}$ connecting the two loops.

### 3.6 Kan complexes and quasi-categories

In this section, we analyze two very well-known model structures on the category of simplicial sets **sSet**; the Kan–Quillen and the Joyal model structures. One interesting feature is that we obtain the same theory for both models, but under the light of theorem 2.38 meaningful statements are delimited by the fibrant objects. In the first model we are interested in Kan complexes, while in the second model in the quasi-categories. The first model appears in [Qui06] and the second in [Joy08]. These are the first references one can find, but the literature is ample for both models.

Recall that a map $f : X \to Y$ between simplicial sets is a *Kan fibration* if it has the right lifting property for all horn inclusions, *i.e.*, the solid diagram below a diagonal filler

$$\begin{array}{c} \Lambda^k[n] \longrightarrow X \\ \downarrow \quad \nearrow \quad \downarrow f \\ \Delta[n] \longrightarrow Y \end{array}$$

for all $0 \le k \le n \in \mathbb{N}$. The simplicial set $X$ is a *Kan complex* if the unique map to the terminal presheaf is a Kan fibration. This is the result from [Qui06]:

**Theorem 3.25.** *The category of simplicial sets* **sSet** *carries a model structure in which:*

1. *Weak equivalences are maps* $f : X \to Y$ *whose geometric realization* $|f| : |X| \to |Y|$ *is a weak homotopy equivalence in the category of topological spaces* **Top**. *These are called Kan equivalences.*

2. *Fibrations are the Kan fibrations.*

43