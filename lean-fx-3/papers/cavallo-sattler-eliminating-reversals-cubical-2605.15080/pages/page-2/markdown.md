2

Eliminating reversals from cubical type theories

$i:\mathbb{I}\vdash\neg i:\mathbb{I}$ such that $\neg 0=1$, $\neg 1=0$, and $\neg\neg i=i$, we can define a path inversion operator

$$\mathsf{sym} := \lambda p.\lambda i.p(\neg i) : (a_0 \sim^A a_1) \to (a_1 \sim^A a_0)$$

that is strictly involutive ($\mathsf{sym} \circ \mathsf{sym} = \mathsf{id}$) and commutes strictly with the action of functions ($\mathsf{cong}_f \circ \mathsf{sym} = \mathsf{sym} \circ \mathsf{cong}_f$). Connections $i:\mathbb{I}, j:\mathbb{I}\vdash i \land j:\mathbb{I}$ and $i:\mathbb{I}, j:\mathbb{I}\vdash i \lor j:\mathbb{I}$ behaving like the min and max functions on the topological interval are similarly useful for higher-dimensional manipulations. Cohen, Coquand, Huber, and Mörtberg's original cubical type theory [12] includes $\neg$, $\land$, and $\lor$ with the equational theory of the free De Morgan algebra. On the other hand, Angiuli, Favonia, and Harper's theory [3] demonstrates that none of these operators is necessary to set up a well-behaved cubical type theory.

While convenient for the user of the type theory, additional operations on the interval are less convenient for the semanticist. To justify the project of synthetic homotopy theory, a cubical type theory should at least have a model in $\infty$-groupoids, an abstract description of the homotopy theory of topological spaces. Constructive models classically equivalent to $\infty$-groupoids were found first for cubical type theory without any interval operations by Awodey, Cavallo, Coquand, Riehl, and Sattler [6] and then for the theory with one connection $\lor$ by Cavallo and Sattler [11]. Most recently, the second-named author announced [32] a model constructively equivalent to $\infty$-groupoids that can interpret cubical type theory with two connections, $\land$ and $\lor$, and the equations of a bounded distributive lattice. However, none of these models interpret a reversal. This is a particularly unfortunate state of affairs because Cubical Agda [41], the most widely used proof assistant for cubical type theory, is based on Cohen et al.'s type theory and thus includes $\neg$ along with $\lor$ and $\land$, and its substantial standard library [36] relies extensively on these operators.

## 1.1 Contributions

We show that a reversal is an essentially harmless extension to cubical type theory.

The key fact is that when $\mathbb{I}$ is an interval object with endpoints 0 and 1, its square $\mathbb{I} \times \mathbb{I}$ is an interval object with endpoints $(0,1)$ and $(1,0)$ and a reversal $\neg(i_0, i_1) := (i_1, i_0)$ that swaps the axes of the square. When $\mathbb{I}$ has connections defining a distributive lattice $(\mathbb{I}, \land, \lor, 0, 1)$, $\mathbb{I} \times \mathbb{I}$ is a De Morgan algebra with connections given by $(i_0, i_1) \land (j_0, j_1) := (i_0 \land j_0, i_1 \lor j_1)$ and $(i_0, i_1) \lor (j_0, j_1) := (i_0 \lor j_0, i_1 \land j_1)$. In general, when $\mathbb{I}$ has some self-dual algebraic structure (in a sense we make precise in Section 4.1), $\mathbb{I} \times \mathbb{I}$ has the same structure as well as a reversal. A variety of constructions in this mold appear in the algebraic literature (e.g., in lattice and order theory), where they are called twist constructions. This name originates with Kracht [23], who applies it to a construction of Nelson algebras from Heyting algebras taken from Vakarelov [40]. Fidel and Brignole [17] and Rivieccio [30, §7] consider the case of building De Morgan algebras from distributive lattices, which is of particular interest to us.

We derive two main results from this simple construction.

### 1.1.1 Conservativity for opaque cubical type theory

First, we prove that a reversal is a conservative extension for "opaque" cubical type theories with self-dual interval theories. Similar to a theory considered by Coquand, Huber, and Sattler [14], these opaque theories are cubical type theories where certain strict equations are either omitted or replaced with terms of path type. Specifically, we

- (a) omit equations that reduce uses of the filling operator at concrete type formers, and
- (b) weaken equations for the reduction of HIT eliminators on path constructors to paths.