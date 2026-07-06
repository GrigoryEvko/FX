CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

*Proof.* As the morphisms $\{\epsilon\} \to [1]$ for $\epsilon \leq 1$ are discrete Conduché functors, pullback along them preserves colimits, and we can then reduce to the case where $C$ is of the shape $[1]^\sharp$ or $[a, 1]$ with $a$ is an element of $t\Theta$. The case $C := [1]^\sharp$ is obvious as we have $[1]^\sharp \otimes [1]^\sharp \sim [1]^\sharp \times [1]^\sharp$ according to the first assertion of proposition 5.1.2.2. We then focus on the case $C := [a, 1]$.

We claim that for any marked $(\infty, \omega)$-category $D$, the square

$$\begin{array}{ccc} \{\epsilon\} & \longrightarrow & [D, 1] \\ \downarrow & & \downarrow \\ \{\epsilon\} & \longrightarrow & [1]^\sharp \end{array} \tag{5.1.3.19}$$

is cartesian. To show this, as the morphisms $\{\epsilon\} \to [1]$, are discrete Conduché functors one can reduce to the case where $D$ is a globular sum, where it is obvious.

We now return to the proof of the assertion. Using the equation (5.1.3.9), the morphism $[a, 1] \otimes [1]^\sharp$ is the horizontal colimit of the following diagram:

$$\begin{array}{ccccccccc} [1]^\sharp \vee [a, 1] & \longleftarrow & [a \otimes \{0\}, 1] & \longrightarrow & [a \otimes [1]^\sharp, 1] & \longleftarrow & [a \otimes \{1\}, 1] & \longrightarrow & [a, 1] \vee [1]^\sharp \\ \downarrow_{a^1} & & \downarrow & & \downarrow & & \downarrow_{a^0} & & \downarrow_{a^0} \\ [1]^\sharp & \longleftarrow & [1]^\sharp & \longrightarrow & [1]^\sharp & \longleftarrow & [1]^\sharp & \longrightarrow & [1]^\sharp \end{array}$$

The results is then a direct application of the cartesian square (5.1.3.19) and of the fact that pullbacks along morphisms $\{\epsilon\} \to [1]$ for $\epsilon \leq 1$ preserves colimits. $\square$

**Proposition 5.1.3.20.** *For any object $a$ of $t\Theta$, the marked $(\infty, \omega)$-categories $a \otimes [1]^\sharp$, $a \star 1$ and $1 \star a$ are strict.*

*Proof.* We will show only the strictness of the object $a \otimes [1]^\sharp$, as the proofs for $a \star 1$ and $1 \star a$ are similar.

Suppose first that $a$ is of shape $b^b$. The first assertion of proposition 5.1.2.2 implies that the underlying $(\infty, \omega)$-categories of $b^b \otimes [1]^\sharp$ is $b \otimes [1]$ which is strict according to proposition 4.3.3.19.

To conclude, we have to show that for any integer $n$, $(\mathbf{D}_n)_t \otimes [1]^\sharp$ is strict. We proceed by induction. Suppose first that $a$ is $(\mathbf{D}_1)_t$. The second assertion of proposition 5.1.2.2 implies that $(\mathbf{D}_1)_t \otimes [1]^\sharp$ is $([1] \times [1])^\sharp$ which is a strict object.

Suppose now that $(\mathbf{D}_n)_t \otimes [1]^\sharp$ is strict. The equation (5.1.3.9) stipulates that $(\mathbf{D}_{n+1})_t \otimes [1]^\sharp$ is the colimit of the diagram.

$$[1]^\sharp \vee [(\mathbf{D}_n)_t, 1] \leftarrow [(\mathbf{D}_n)_t \otimes \{0\}, 1] \rightarrow [(\mathbf{D}_n)_t \otimes [1]^\sharp, 1] \leftarrow [(\mathbf{D}_n)_t \otimes \{1\}, 1] \rightarrow [\mathbf{D}_n)_t, 1] \vee [1]^\sharp$$

The induction hypothesis and the proposition 4.3.3.2 implies that all the objects are strict. According to proposition 5.1.1.37, whose hypotheses are provided by lemma 5.1.3.18, this

252