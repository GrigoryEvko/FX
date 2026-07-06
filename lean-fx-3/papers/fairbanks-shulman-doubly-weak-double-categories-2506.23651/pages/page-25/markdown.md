DOUBLY WEAK DOUBLE CATEGORIES

25

Finally, we let $T_2^{\mathbf{I}}$ be the coequalizer of the two maps $FB \Rightarrow FA$ in $\mathbf{Mnd}_f(2\text{-Cptd})$. Then a $T_2^{\mathbf{I}}$-algebra is an $FA$-algebra $X$ whose two underlying $FB$-algebra structures are equal. In the case of associativity, this says precisely that the two possible composites of a vertically composable trio are equal in $X$, i.e. that $X$ obeys the associativity axiom; and similarly for the other axioms. Thus, $T_2^{\mathbf{I}}$-algebras are precisely implicit 2-categories as defined above.

As usual, we could give an equivalent “unbiased” definition using $n$-ary compositions, rather than just binary and nullary composition. This would lead to a different presentation, but an isomorphic monad.

The double-categorical case is entirely analogous, leading to a monad $T_{\mathbf{d}}^{\mathbf{I}}$ on **DblCptd** whose algebras are implicit double categories.

**Definition 5.2.** An **implicit double category** is a double computad $X$ with

- horizontal composition operations

$$X(2_{c,d}^{a,x}) \times_1 X(2_{x,d'}^{a',b'}) \rightarrow X(2_{c,d+d'}^{a+a',b'})$$

(where the vertical target 1-cell path of the first factor is identified with the vertical source 1-cell path of the second factor),

- horizontal identity operations

$$X(1^V) \times_0 \cdots \times_0 X(1^V) \rightarrow X(2_{n,0}^{0,n})$$

(where the domain is length $n$ paths of vertical 1-cells),

- vertical composition operations

$$X(2_{c,x}^{a,b}) \times_1 X(2_{c',d'}^{x,b'}) \rightarrow X(2_{c+c',d'}^{a,b+b'})$$

(where the horizontal target 1-cell path of the first factor is identified with the horizontal source 1-cell path of the second factor), and

- vertical identity operations

$$X(1^H) \times_0 \cdots \times_0 X(1^H) \rightarrow X(2_{0,n}^{n,0})$$

(where the domain is length $n$ paths of horizontal 1-cells)

satisfying source and target laws, associativity and unit laws, and interchange laws.

These definitions agree with those of Sections 2 and 3, since we have observed that 2-computads and double computads can be identified with 2-graphs and double graphs equipped with free category structure via the functors $\iota_2$ and $\iota_{\mathbf{d}}$, and the 2-cell operations and laws given here exactly enhance this to 2-category or double category structure.

*Remark 5.3.* We can also describe these monads in a more conceptual way. Observe that the free 2-category monad on **1-Cat-2-Gph** (2-graphs equipped with 1-category structure) restricts to the subcategory **2-Cptd** (2-graphs equipped with free 1-category structure and maps sending generating 1-cells to generating 1-cells); indeed, this free 2-category monad acts as identity on underlying 1-category structure. The algebras of this monad on **2-Cptd** are simply algebras of the monad on **1-Cat-2-Gph** that lie within the subcategory **2-Cptd**, namely those 2-categories with free underlying 1-categories; algebra morphisms are restricted to those that lie within the subcategory **2-Cptd**, namely those sending generating 1-cells to generating 1-cells. But these are precisely implicit 2-categories and their functors as