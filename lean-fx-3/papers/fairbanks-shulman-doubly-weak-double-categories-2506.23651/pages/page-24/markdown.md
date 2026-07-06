24

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

As an example, we start with a definition of implicit 2-categories.

**Definition 5.1.** An **implicit 2-category** is a 2-computed $X$ equipped with

- horizontal composition operations

$$X(2^n)_n \times_0 X(2^{m'}_{n'}) \rightarrow X(2^{m+n'}_{n+n'})$$

(where the target 0-cell of the first factor is identified with the source 0-cell of the second factor),

- vertical composition operations

$$X(2^x_x)_x \times_1 X(2^x_n) \rightarrow X(2^n_n)$$

(where the target 1-cell path of the first factor is identified with the source 1-cell path of the second factor), and

- identity operations

$$\overbrace{X(1) \times_0 \cdots \times_0 X(1)}^n \rightarrow X(2^n_n)$$

(where the domain is length $n$ paths of 1-cells)

satisfying source and target laws, associativity and unit laws, and interchange laws.

To go from this definition to a monad on **2-Cptd** whose algebras are implicit 2-categories, we start with the following family $A \in [\text{ob } 2\text{-Cptd}_f, 2\text{-Cptd}]$, where we identify objects of $\mathbb{C}_1$ with their corresponding representable functors in **2-Cptd**:

$$Ac = \begin{cases} 2^{m+n'}_{n+n'} & \text{if } c = 2^n_n \sqcup_0 2^{m'}_{n'} \\ 2^n_n & \text{if } c = 2^x_x \sqcup_1 2^x_n \\ 2^n_n & \text{if } c = \overbrace{1 \sqcup_0 \cdots \sqcup_0 1}^n \end{cases}$$

(Note that all representables are finitely presentable, and pushouts of finitely presentable objects are finitely presentable.) Then an $FA$-algebra is a 2-computed $X$ equipped with three families of maps. The first consists of maps

$$2\text{-Cptd}(2^n_n \sqcup_0 2^{m'}_{n'}, X) \rightarrow 2\text{-Cptd}(2^{m+n'}_{n+n'}, X)$$

But by the universal property of colimits and the Yoneda lemma, this is equivalent to a map

$$X(2^n_n) \times_0 X(2^{m'}_{n'}) \rightarrow X(2^{m+n'}_{n+n'})$$

as in **Definition 5.1** above. The other two families similarly correspond to the other families of operations in **Definition 5.1**. An $FA$-algebra is then a 2-computed equipped with all these operations, but not satisfying any axioms.

To impose the axioms on such a structure, we specify another family $B \in [\text{ob } 2\text{-Cptd}_f, 2\text{-Cptd}]$ and a pair of morphisms $B \Rightarrow UFA$ in $[\text{ob } 2\text{-Cptd}_f, 2\text{-Cptd}]$, where $U$ is the forgetful right adjoint to $F$. For instance, the contribution to $B$ for associativity of vertical composition is

$$B(2^x_x \sqcup_1 2^y_x \sqcup_1 2^y_n) = 2^n_n.$$

We must then specify two morphisms $2^n_n \rightarrow FA(2^x_x \sqcup_1 2^y_x \sqcup_1 2^y_n)$, which is to say two 2-cells of shape $2^n_n$ in the free $FA$-algebra on a trio of 2-cells that could be composed to give one of shape $2^n_n$. In an $FA$-algebra, there are two ways to bracket the composition of such a trio that are not equal; we take these two bracketed compositions as the two desired 2-cells. All the other axioms are treated similarly.