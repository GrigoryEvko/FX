We want to show that $x$ and $y$ can be lifted to $X$.

One first remarks that as $X$ is fibrant, the equation $\Lambda P \rightarrow P$ has solutions in $X$ according to Proposition 3.25. This implies that one can find a lift $(x', y'): P \rightarrow X$ that makes the upper triangle commutative.

Now, in $Y$, we have two solutions of the equation $\Lambda P \rightarrow P$, given by $(\pi(x'), \pi(y'))$ and $(x, y)$. As $Y$ is fibrant, $P \coprod_{\Lambda P} P \rightarrow \text{Uni}_{\Lambda P}^{coh}(P)$ has solutions in $Y$, and there exist marked arrows:

$$z: x \rightarrow \pi(x')$$

$$w: s\#_n \pi(y') \rightarrow y$$

where $s$ is by construction a composite of $z$ with arrows in the source of $\pi(y')$.

By the isofibration property, there exists an arrow

$$\overline{z}: \overline{x} \rightarrow x'$$

over $z$. This arrow induces an arrow $\overline{s}$ over $s$. By the dual isofibration property from Lemma 3.28, there exists an arrow

$$\overline{w}: s\#_n y' \rightarrow \overline{y}$$

over $w$. The pair $(\overline{x}, \overline{y})$ then induces the desired lift $P \rightarrow X$.

Now, to show that isofibrations have the right lifting property against saturations, one simply remarks that lifts against saturations are unique when they exist (saturations are epimorphisms), so as fibrant objects have the right lifting property against these maps, any map between fibrant objects also has the lifting property against all saturations. $\square$

### 3.30 Proposition. *A morphism between fibrant $m$-marked $\infty$-categories is a fibration if and only if it is an isofibration.*

*Proof.* According to Lemma 2.46, the morphism $i_n^+$ is an anodyne cofibration, so all fibrations (between fibrant objects) are isofibrations.

For the converse, as a morphism between fibrant objects is a fibration if and only if it has the right lifting property against generating anodyne cofibrations, which are either equations or saturations, Lemma 3.29 implies that isofibrations between fibrant objects are fibrations. $\square$

As a consequence, we have:

### 3.31 Corollary. *Equations and saturations are acyclic cofibrations.*

*Proof.* The Lemma 3.29 and the Lemma 3.29 implies that equations and saturations have the lifting property against fibration between fibrants. By definition, this implies that these maps are acyclic cofibrations. $\square$

32