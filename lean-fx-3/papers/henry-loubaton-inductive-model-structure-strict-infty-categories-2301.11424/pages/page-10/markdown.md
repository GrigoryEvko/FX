## 2.7 Definition.

- We say that an $\infty$-category $X$ is a polygraph if it can be constructed from the empty $\infty$-category by freely adding arrows with specified source and target. That is, $X$ can be obtained as a transfinite composition $\emptyset = X_0 \to X_1 \to \cdots \to X_i \to \operatorname{Colim} X_i = X$, where for each $i$, the map $X_i \to X_{i+1}$ is a pushout of $\coprod_S \partial \mathbb{D}_n \to \coprod_S \mathbb{D}_{n+1}$.
- An arrow of a polygraph is said to be a *generator* if it is one of the arrows that has been freely added at some stage.
- A morphism of $\infty$-categories between two polygraphs is said to be a *morphism of polygraphs* or a *polygraphic morphism* if it sends each generator to a generator.
- An $n$-polygraph is a polygraph whose generators are all of dimension less than or equal to $n$.

**2.8 Remark.** Generators of a polygraph can be shown to be exactly the arrows that cannot be written as a composite in a non-trivial way$^3$, see 16.6.1 and 16.6.2 in [4].

So, the notion of generator does not depend on the choice of the presentation of $X$, and any isomorphism between polygraphs is automatically polygraphic, see 16.6.3 in [4].

**2.9 Example.** The only $n$-polygraph for $n < 0$ is the empty $\infty$-category. The category of 0-polygraphs is equivalent to the category of sets and corresponds to discrete $\infty$-categories. The category of 1-polygraphs (and polygraphic morphisms between them) is equivalent to the category of directed graphs, and they correspond to categories that are free on a graph.

We will sometimes distinguish between a polygraph seen as an object of the category of polygraphs and polygraphic morphisms, and the corresponding $\infty$-category, which we call the free $\infty$-category on the polygraph.

**2.10 Remark.** Each arrow in a polygraph can be written as an iterated composite of the generators (not necessarily in a unique way). For an $n$-arrow $f$, the set of generators of dimension $n$ that appear in such an expression, and even the number of times they appear, is the same for all such expressions, see section 4.3 of [35]. We will say that an $n$-generator *appears* in an $n$-arrow if it appears in any such expression.

**2.11 Construction.** The category $\infty$-Cat admits a closed monoidal structure, called the Gray tensor product or Crans-Gray tensor product, which we denote as

$$\begin{array}{c c c} \infty\text{-Cat} \times \infty\text{-Cat} & \to & \infty\text{-Cat} \\ X, Y & \mapsto & X \otimes Y \end{array}$$

Its explicit construction is very involved, and we will assume the reader is already familiar with it. It was first introduced by S. Crans in his Ph.D. thesis [16]. We refer to [1] for an introduction to this tensor product close to its original definition, and to [40] for a more modern account. The proof of the existence of this monoidal structure in [40] contains some gaps that have been fixed in Appendix A of [6].

$^3$The trivial ones being decompositions involving units, such as the decompositions $u = u\#_i \mathbb{I}_{u_i^+ u}^k = \mathbb{I}_{u_i^- u}^k \#_i u$.

10