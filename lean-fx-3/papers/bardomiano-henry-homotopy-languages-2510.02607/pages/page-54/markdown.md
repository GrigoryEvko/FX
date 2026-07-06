**Proposition 3.38.** *The Reedy model structure on $\mathcal{C}_{Reedy}^{([1]_+)^{\mathrm{op}}}$ coincides with the injective model structure. In particular, weak equivalences and cofibrations are the level-wise weak equivalences and cofibrations in $\mathcal{C}$.*

*Proof.* The result is folklore. $\square$

We find that fibrant objects are those such that $X_0 \to X_1$ is an isofibration. Therefore, the language in this case refers to isofibrations. Again, this model structure has generating cofibrations

$$\{d_0 \hat{\otimes} u, d_0 \hat{\otimes} v, d_0 \hat{\otimes} w, d_1 \hat{\otimes} u, d_1 \hat{\otimes} v, d_1 \hat{\otimes} w\}.$$

Next, observe that $\partial \updownarrow_0 = 0$ and $\partial \updownarrow_1 = \updownarrow_0$. We have the maps $d_0 : 0 \to \updownarrow_0$ and $d_1 : \updownarrow_0 \to \updownarrow_1$. Therefore, if $i : a \to b \in I$, then this give us the following cofibrations

- $\updownarrow_0 \otimes a \to \updownarrow_0 \otimes b$,
- $\updownarrow_1 \otimes a \coprod_{\updownarrow_0 \otimes a} \updownarrow_0 \otimes b \to \updownarrow_1 \otimes b$.

The map $\updownarrow_0 \otimes a \to \updownarrow_0 \otimes b$ for $i \in I$ corresponds to the following type introduction:

$$\vdash X_0 \text{ Type} \quad x, y : X_0 \vdash X_0(x, y) \text{ Type} \quad x, y : X_0, f, g : X_0(x, y) \vdash f =_{X_0} g \text{ Type}$$

which we can think of as a category. The analysis of the second map is more intricate. Let us denote the evaluation of the representables by $\updownarrow_{k0}$ and $\updownarrow_{k1}$ for $k = 0, 1$, and for simplicity we keep the '$\otimes$' symbol. Evaluating the cofibration $\updownarrow_1 \otimes a \coprod_{\updownarrow_0 \otimes a} \updownarrow_0 \otimes b \to \updownarrow_1 \otimes b$ at $[1]_+^\mathrm{op}$ give us the square,

$$\begin{array}{ccc} \updownarrow_{11} \otimes a \coprod_{\updownarrow_{10} \otimes a} \updownarrow_{10} \otimes b & \longrightarrow & \updownarrow_{01} \otimes a \coprod_{\updownarrow_{00} \otimes a} \updownarrow_{00} \otimes b \\ \updownarrow & & \updownarrow \\ \updownarrow_{11} \otimes b & \longrightarrow & \updownarrow_{01} \otimes b, \end{array}$$

where the horizontal arrows are induced by the diagram $[1]_+^\mathrm{op}$. This simplifies to

$$\begin{array}{ccc} a & \longrightarrow & a \coprod_a b \\ \updownarrow & & \updownarrow \\ b & \longrightarrow & b, \end{array}$$

54