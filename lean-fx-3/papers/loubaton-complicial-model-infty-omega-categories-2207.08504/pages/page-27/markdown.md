1.2. GRAY OPERATIONS

Construction 1.2.1.6. We define the functor $\nu : \mathrm{ADC} \to \omega$-cat which associates to an augmented directed complex $K$, the $\omega$-category $\nu K$, and to a morphism of augmented directed complexes $f : K \to L$, the morphism of $\omega$-categories.

$$\begin{array}{c c c c c} \nu f : & \nu K & \to & \nu L \\ & \left( \begin{array}{c c c} x _ {0} ^ {-} & \dots & x _ {n} ^ {-} \\ x _ {0} ^ {+} & \dots & x _ {n} ^ {+} \end{array} \right) & \mapsto & \left( \begin{array}{c c c} f _ {0} (x _ {0} ^ {-}) & \dots & f _ {n} (x _ {n} ^ {-}) \\ f _ {0} (x _ {0} ^ {+}) & \dots & f _ {n} (x _ {n} ^ {+}) \end{array} \right) \end{array}$$

Theorem 1.2.1.7 (Steiner). The functors $\lambda$ and $\nu$ form an adjoint pair

$$\lambda : \omega\text{-cat} \xrightarrow{\quad} \mathrm{ADC} : \nu$$

For a $\omega$-category $C$, the unit of the adjunction is given by:

$$\begin{array}{r c l} \eta : & C & \to \quad \nu \lambda C \\ & x \in C _ {n} & \mapsto \quad \left( \begin{array}{c c c} [ d _ {0} ^ {-} (x) ] _ {0} & \dots & [ d _ {n - 1} ^ {-} (x) ] _ {n - 1} \\ [ d _ {0} ^ {+} (x) ] _ {0} & \dots & [ d _ {n - 1} ^ {+} (x) ] _ {n - 1} \end{array} \right) \end{array}$$

For an augmented directed complex $K$, the counit is given by:

$$\begin{array}{r c l} \pi : & \lambda \nu K & \to \quad K \\ & [ x ] _ {n} \in (\lambda \nu K) _ {n} & \mapsto \quad x _ {n} ^ {+} = x _ {n} ^ {-} \end{array}$$

Proof. This is [Ste04, theorem 2.11].

Definition 1.2.1.8. A basis for an augmented directed complex $(K, K^{*}, e)$ is a graded set $B = (B_{n})_{n \in \mathbb{N}}$ such that for every $n$, $B_{n}$ is both a basis for the monoid $K_{n}^{*}$ and for the group $K_{n}$.

Remark 1.2.1.9. The elements of $B_{n}$ can be characterized as the minimal elements of $K_{n}^{*}\backslash 0$ for the following order relation:

$$x \leq y \text { iff } y - x \in K _ {n} ^ {*}$$

This shows that if a basis exists, it is unique.

Any element of $K_{n}$ can then be written uniquely as a sum $\sum_{b\in B_n}\lambda_b b$. This leads us to define new operations:

Definition 1.2.1.10. For an element $x := \sum_{b \in B_n} \lambda_b b$ of $K_n$, we define the positive part and the negative part:

$$\begin{array}{l} (x) _ {+} := \sum_ {b \in B _ {n}, \lambda_ {b} > 0} \lambda_ {b} b \\ (x) _ {-} := \sum_ {b \in B _ {n}, \lambda_ {b} < 0} - \lambda_ {b} b \end{array}$$

We then have $x = (x)_{+} - (x)_{-}$. An element $x$ is positive (resp. negative) when $x = (x)_{+}$ (resp. when $x = -(x)_{-}$). Let $y = \sum_{b \in B_n} \mu_b b$, we set :

$$x \wedge y := \sum_ {b \in B _ {n}} \min (\lambda_ {b}, \mu_ {b}) b$$

Eventually, we set

$$\begin{array}{l} \partial_ {n} ^ {+} (\_) := (\partial_ {n} (\_)) _ {+}: K _ {n + 1} \to K _ {n} ^ {*} \\ \partial_ {n} ^ {-} (\_) := (\partial_ {n} (\_)) _ {-}: K _ {n + 1} \to K _ {n} ^ {*} \end{array}$$

When an element $b$ of the basis is in the support of $x$, i.e $\lambda_{b} \neq 0$, we say that $b$ belongs to $x$, which is denoted by $b \in x$.

27