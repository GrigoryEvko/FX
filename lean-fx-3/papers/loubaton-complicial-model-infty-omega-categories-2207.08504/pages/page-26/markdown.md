CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

(2) The augmented directed complex λ[n] has for underlying chain complex:

$$\mathbb{Z} \stackrel{e}{\leftarrow} \mathbb{Z}[v_0, v_1, ..., v_n] \stackrel{\partial_0}{\leftarrow} \mathbb{Z}[v_{0,1}, v_{1,2}..., v_{n-1,n}] \stackrel{\partial_1}{\leftarrow} 0 \leftarrow ...$$

where for any k < n and α ∈ {−,+}

$$e(v_k) = e(v_n) = 1 \quad \partial_1(v_{k,k+1}) = v_{k+1} - v_k.$$

Definition 1.2.1.4. We now define the functor ν : ADC → ω-cat. Throughout, we fix an augmented directed complex (K, K*, e). A Steiner array (or simply a array) of dimension n is the data of a finite double sequence:

$$\begin{pmatrix} x_0^- & x_1^- & x_2^- & x_3^- & ... & x_n^- \\ x_0^+ & x_1^+ & x_2^+ & x_3^+ & ... & x_n^+ \end{pmatrix}$$

such that

(1) $x_n^- = x_n^+$;
(2) For any $i \le n$ and α ∈ {−,+}, $x_i^\alpha$ is an element of $K_i^*$;
(3) For any $0 < i \le n$, $\partial_{i-1}(x_i^\alpha) = x_{i-1}^+ - x_{i-1}^-$;

An array is said to be coherent if $e(x_0^+) = e(x_0^-) = 1$.

Definition 1.2.1.5. We define the globular set νK, whose n-cells are the coherent arrays of dimension n. The source and target maps are defined for k < n by the formula:

$$d_k^\alpha \begin{pmatrix} x_0^- & x_1^- & x_2^- & ... & x_n^- \\ x_0^+ & x_1^+ & x_2^+ & ... & x_n^+ \end{pmatrix} = \begin{pmatrix} x_0^- & x_1^- & x_2^- & ... & x_{k-1}^- & x_k^\alpha \\ x_0^+ & x_1^+ & x_2^+ & ... & x_{k-1}^+ & x_k^\alpha \end{pmatrix}$$

There is an obvious group structure on the arrays:

$$\begin{pmatrix} x_0^- & x_1^- & ... & x_n^- \\ x_0^+ & x_1^+ & ... & x_n^+ \end{pmatrix} + \begin{pmatrix} y_0^- & y_1^- & ... & y_n^- \\ y_0^+ & y_1^+ & ... & y_n^+ \end{pmatrix} = \begin{pmatrix} x_0^- + y_0^- & x_1^- + y_1^- & ... & x_n^- + y_n^- \\ x_0^+ + y_0^+ & x_1^+ + y_1^+ & ... & x_n^+ + y_n^+ \end{pmatrix}$$

- For two coherent arrays x and y such that $d_k^-(x) = d_k^+(y) = z$, we define their k-composition by the following formula:

$$x *_k y := x - z + y.$$

More explicitly:

$$\begin{pmatrix} x_0^- & ... & x_n^- \\ x_0^+ & ... & x_n^+ \end{pmatrix} *_k \begin{pmatrix} y_0^- & ... & y_n^- \\ y_0^+ & ... & y_n^+ \end{pmatrix} := \begin{pmatrix} y_0^- & ... & y_k^- & y_{k+1}^- + x_{k+1}^- & ... & y_n^- + x_n^- \\ x_0^+ & ... & x_k^+ & y_{k+1}^+ + x_{k+1}^+ & ... & y_n^+ + x_n^+ \end{pmatrix}$$

- For an integer m > n, we define the m-sized array $1_x^m$ as follows:

$$1_x^m := \begin{pmatrix} x_0^- & ... & x_n^- & 0 & ... & 0 \\ x_0^+ & ... & x_n^+ & 0 & ... & 0 \end{pmatrix}$$

The globular set νK, equipped with these compositions and units is an ω-category.

26