3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

Construction 3.2.1.2. We extend $e \star \_$ as a functor

$$e \star \_ : \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$$

by setting $e \star [e, 1]_t$ as the colimit

$$\begin{array}{c} [e, 1] \xrightarrow{d^0 \star [e, 1]} \tau_1^i(e \star [e, 1]) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [e, 1]_t \longrightarrow e \star [e, 1]_t \end{array}$$

The natural transformation $d^0 \star \_$ extends to a transformation

$$d^0 \star C : C \to e \star C$$

natural in $C : \mathrm{tSeg}(A)$.

Proposition 3.2.1.3. For any stratified Segal $A$-precategory $X$, there exists a weak equivalence

$$\{0\} \coprod_{\{0\} \otimes X} [1] \otimes X \to e \star X$$

natural in $X$.

Proof. As the two functors $\{0\} \coprod_{\{0\} \otimes \_} [1] \otimes \_$ and $e \star \_$ are left Quillen functors, it is sufficient to construct this comparison when $C$ is of shape $[a, n]$ or $[e, 1]_t$. In this case, the canonical morphism $[1] \otimes [n] \to 1 \star [n]$ of $(0, \omega)$-categories induces comparison morphisms

$$[1] \otimes [a, n] \to e \star [a, n] \quad [1] \otimes [e, 1]_t \to e \star [e, 1]_t$$

that respectively send $\{0\} \otimes [a, n]$ and $\{0\} \otimes [e, 1]_t$ to $e \star \emptyset$. The two previous morphisms then induce natural morphisms

$$\{0\} \coprod_{\{0\} \otimes [a, n]} [1] \otimes [a, n] \to e \star [a, n] \qquad \{0\} \coprod_{\{0\} \otimes [e, 1]_t} [1] \otimes [e, 1]_t \to e \star [e, 1]_t$$

Now, remark that these two morphisms fit in the following cocartesian squares:

$$\begin{array}{c} \operatorname{colim}_{[k_0], k_1] \to \{0\} \coprod_{\{0\} \otimes [n]} [1] \otimes [n]} [[k_0] \otimes a, k_1] \longrightarrow e \coprod_{\{0\} \otimes [a, n]} [1] \otimes [a, n] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \operatorname{colim}_{[k_0], k_1] \to 1 \star [n]} [[k_0] \otimes a, k_1] \longrightarrow e \star [a, n] \\ \operatorname{colim}_{[k_0], k_1] \to \{0\} \coprod_{\{0\} \otimes [1]} [1] \otimes [1]} [[k_0] \otimes a, k_1] \longrightarrow e \coprod_{\{0\} \otimes [a, n]} [1] \otimes [e, 1]_t \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \operatorname{colim}_{[k_0], k_1] \to 1 \star [1]} [[k_0] \otimes a, k_1] \longrightarrow e \star [e, 1]_t \end{array}$$

We claim that the functor whose value on a $\Theta_2$-set $X$ is $\operatorname{colim}_{[k_0], k_1] \to X} [[k_0] \otimes a, k_1]$ sends $\overline{\mathrm{W}_2}$ to weak equivalences. Combined with proposition 1.2.5.23, it will conclude the proof.

To show the desired claim, remark that this functor is the composite

$$\operatorname{Psh}(\Theta_2) \xrightarrow{1^*} \operatorname{Psh}(\Delta[\Delta]) \cong \operatorname{Seg}(\operatorname{Psh}(\Delta)) \xrightarrow{\operatorname{Seg}(\_ \otimes a)} \operatorname{Seg}(A)$$

and the results follow from propositions 1.1.3.17 and 2.1.1.8.

115