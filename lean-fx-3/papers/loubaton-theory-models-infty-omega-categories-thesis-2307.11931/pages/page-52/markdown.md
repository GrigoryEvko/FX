CHAPTER 1. THE CATEGORY OF \((0,\omega)\)-CATEGORIES

(2) For any \(i \leq n\) and \(\alpha \in \{-, +\}\), \(x_i^\alpha\) is an element of \(K_i^*\);
(3) For any \(0 < i \leq n\), \(\partial_{i-1}(x_i^\alpha) = x_{i-1}^+ - x_{i-1}^-\);

An array is said to be coherent if $e(x_0^+) = e(x_0^-) = 1$.

Definition 1.2.1.5. We define the globular set $\nu K$, whose $n$-cells are the coherent arrays of dimension $n$. The source and target maps are defined for $k < n$ by the formula:

$$d_k^\alpha \begin{pmatrix} x_0^- & x_1^- & x_2^- & \dots & x_n^- \\ x_0^+ & x_1^+ & x_2^+ & \dots & x_n^+ \end{pmatrix} = \begin{pmatrix} x_0^- & x_1^- & x_2^- & \dots & x_{k-1}^- & x_k^\alpha \\ x_0^+ & x_1^+ & x_2^+ & \dots & x_{k-1}^+ & x_k^\alpha \end{pmatrix}$$

There is an obvious group structure on the arrays:

$$\begin{pmatrix} x_0^- & x_1^- & \dots & x_n^- \\ x_0^+ & x_1^+ & \dots & x_n^+ \end{pmatrix} + \begin{pmatrix} y_0^- & y_1^- & \dots & y_n^- \\ y_0^+ & y_1^+ & \dots & y_n^+ \end{pmatrix} = \begin{pmatrix} x_0^- + y_0^- & x_1^- + y_1^- & \dots & x_n^- + y_n^- \\ x_0^+ + y_0^+ & x_1^+ + y_1^+ & \dots & x_n^+ + y_n^+ \end{pmatrix}$$

- For two coherent arrays $x$ and $y$ such that $d_k^-(x) = d_k^+(y) = z$, we define their $k$-composition by the following formula:

$$x *_k y := x - z + y.$$

More explicitly:

$$\begin{pmatrix} x_0^- & \dots & x_n^- \\ x_0^+ & \dots & x_n^+ \end{pmatrix} *_k \begin{pmatrix} y_0^- & \dots & y_n^- \\ y_0^+ & \dots & y_n^+ \end{pmatrix} := \begin{pmatrix} y_0^- & \dots & y_k^- & y_{k+1}^- + x_{k+1}^- & \dots & y_n^- + x_n^- \\ x_0^+ & \dots & x_k^+ & y_{k+1}^+ + x_{k+1}^+ & \dots & y_n^+ + x_n^+ \end{pmatrix}$$

- For an integer $m > n$, we define the $m$-sized array $1_x^m$ as follows:

$$1_x^m := \begin{pmatrix} x_0^- & \dots & x_n^- & 0 & \dots & 0 \\ x_0^+ & \dots & x_n^+ & 0 & \dots & 0 \end{pmatrix}$$

The globular set $\nu K$, equipped with these compositions and units is an $\omega$-category.

Definition 1.2.1.6. We define the functor $\nu : \text{ADC} \to \omega$-cat which associates to an augmented directed complex $K$, the $\omega$-category $\nu K$, and to a morphism of augmented directed complexes $f : K \to L$, the morphism of $\omega$-categories.

$$\begin{array}{c c c c c c} \nu f : & \nu K & \to & \nu L \\ & \begin{pmatrix} x_0^- & \dots & x_n^- \\ x_0^+ & \dots & x_n^+ \end{pmatrix} & \mapsto & \begin{pmatrix} f_0(x_0^-) & \dots & f_n(x_n^-) \\ f_0(x_0^+) & \dots & f_n(x_n^+) \end{pmatrix} \end{array}$$

42