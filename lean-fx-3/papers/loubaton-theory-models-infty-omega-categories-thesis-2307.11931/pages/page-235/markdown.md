4.3. GRAY OPERATIONS

and that the basis of $\lambda[n]$ also admits is given by the graded set

$$(B_{\lambda\mathbf{D}_n})_k := \begin{cases} \{v_0, v_1, ..., v_n\} & \text{if } k = 0 \\ \{v_{0,1}, v_{1,2}..., v_{n-1,n}\} & \text{if } k = 1 \\ \emptyset & \text{if } k > 1 \end{cases}$$

We will suppose that $n$ is odd as the proof for $n$ even is similar. As the right vertical morphism is an injection, we just have to show the existence of the lifting.

There exists a unique sequence $\{b_0, ..., b_{l-1}\}$ of element of $(\lambda b)_{n-1}$ and a unique sequence $\{c_0, ..., c_l\}$ of element of $(\lambda b)_n$ such that

$$f(e_n) = b_0 \otimes v_{0,1} + ... + b_{l-1} \otimes v_{l-1,l} + c_0 \otimes v_0 + ... + c_l \otimes v_l$$

The commutativity of the square then implies that the cell

$$\partial b_0 \otimes v_{0,1} + ... + \partial b_{l-1} \otimes v_{l-1,l} + (\partial c_0 - b_0) \otimes v_0 + (\partial c_1 + b_0 - b_1) \otimes v_1... + (\partial c_l + b_l) \otimes v_l$$

is in the image of $\lambda a \otimes \lambda i$. As a consequence, for any $j < k$, we have

$$\begin{cases} \partial b_0 = \partial b_1 = ... = \partial b_{i(0)-1} \\ \partial b_{i(j)} = \partial b_{i(j)+1}... = \partial b_{i(j+1)-1} \quad \text{for } j < k \\ \partial b_{i(k)} = \partial b_{i(k)+1} = ... = \partial b_{l-1} \end{cases}$$

and

$$\begin{cases} \partial c_0 - b_0 = 0 & \text{if 0 is not in the image of } i \\ \partial c_p + b_{p-1} - b_p = 0 & \text{if } p > 0 \text{ is not in the image of } i \\ \partial c_l + b_{l-1} = 0 & \text{if } l \text{ is not in the image of } i \end{cases}$$

The first set of equations forces the equalities:

$$\begin{cases} b_0 = b_1 = ... = b_{i(0)-1} \\ b_{i(j)} = b_{i(j)+1}... = b_{i(j+1)-1} \quad \text{for } j < k \\ b_{i(k)} = b_{i(k)+1} = ... = b_{l-1} \end{cases}$$

Combined with the second set of equations this implies that $c_p$ is null whenever $p$ is not in the image of $i$. We then have

$$f(e_n) = b_{i(0)} \otimes \lambda i(v_{0,1}) + ... + b_{i(k)} \otimes \lambda i(v_{k-1,k}) + c_{i(0)} \otimes \lambda i(v_0) + ... + c_i(k) \otimes \lambda i(v_k)$$

We then define the morphism $l$ as the unique morphism extending $g$ and that fulfills

$$l_n(e_n) := b_{i(0)} \otimes v_{0,1} + ... + b_{i(k)} \otimes v_{k-1,k} + c_{i(0)} \otimes v_0 + ... + c_i(k) \otimes v_k$$

This morphism is the wanted lift.

225