invertible in a weak sense. In this interpretation, marked arrows should correspond to weakly invertible arrows. When $m = \infty$, it still retains an 'inductive' notion of invertibility, like what is expected of the limit of the $\tau$-tower as mentioned in Section 1.2.

However, it is not quite the case yet due to a small defect: Given $X$ a fibrant object, there might be arrows in $X$ that are invertible up to higher marked arrows without being marked themselves. Hence, the fibrant objects are carrying an additional piece of data compared to what $(\infty, n)$-categories should be: some of their invertible arrows are marked and others are not.

To solve this problem, in Section 3.5 we consider a left Bousfield localization $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$, called the *saturated inductive model structure*, in which the fibrant objects are the marked $\infty$-categories in which an arrow is marked if and only if it is invertible up to higher-dimensional marked arrows. These are really our intended model for strict $(\infty, n)$-categories. So we have a first (identity) left Quillen functor:

$$\infty\text{-Cat}_{\text{Ind}}^{+m} \rightarrow \infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$$

We consider the saturated inductive model structure $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$ to be the most interesting one, as it actually models strict $(\infty, m)$-categories. The only reason we use $\infty\text{-Cat}_{\text{Ind}}^{+m}$ is because it is the one that naturally arises from our construction in Section 2.4. It is not completely clear to us what $\infty\text{-Cat}_{\text{Ind}}^{+m}$ actually models at a homotopy theoretic level.

In Section 4.1, we study how these model structures relate when $m$ varies. We show that for $m < p \leqslant \infty$, the obvious inclusion functor $\iota_p: \infty\text{-Cat}^{+m} \subset \infty\text{-Cat}^{+p}$ has both a left adjoint $\pi_m$ and a right adjoint $\tau_m: \infty\text{-Cat}^{+p} \rightarrow \infty\text{-Cat}^{+m}$. We show that these form two Quillen adjunctions $(\pi_m \dashv \iota_p)$ and $(\iota_p \dashv \tau_m)$ between the saturated inductive model structures.

We also investigate how the saturated inductive model structure $\infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty}$ can be understood as a certain limit of the tower of right Quillen functors

$$\infty\text{-Cat}_{\text{Sat-Ind}}^{+0} \stackrel{\tau_n}{\leftarrow} \infty\text{-Cat}_{\text{Sat-Ind}}^{+1} \stackrel{\tau_1}{\leftarrow} \infty\text{-Cat}_{\text{Sat-Ind}}^{+2} \stackrel{\tau_2}{\leftarrow} \dots \stackrel{\tau_{\ell-1}}{\leftarrow} \infty\text{-Cat}_{\text{Sat-Ind}}^{+n} \stackrel{\tau_n}{\leftarrow} \dots$$

as explained previously.

Next, in Section 4.2, in the case where $m = +\infty$, we can take a further left Bousfield localization, which we study in Section 4.2, called the coinductive model structure, denoted $\infty\text{-Cat}_{\text{Coind}}^{+\infty}$, whose fibrant objects are marked $\infty$-categories where the marked arrows are exactly the 'coinductively invertible arrows' (see Definition 4.16):

$$\infty\text{-Cat}_{\text{Ind}}^{+\infty} \rightarrow \infty\text{-Cat}_{\text{Sat-Ind}}^{+\infty} \rightarrow \infty\text{-Cat}_{\text{Coind}}^{+\infty}$$

Of course, we can also try to define $\infty\text{-Cat}_{\text{Coind}}^{+m}$ for finite $m$, but this is the same as $\infty\text{-Cat}_{\text{Sat-Ind}}^{+m}$.

This second localization $\infty\text{-Cat}_{\text{Coind}}^{+\infty}$ is in fact equivalent to the canonical model structure on $\infty$-categories $\infty\text{-Cat}_{\text{Can}}$ from [30], in a fairly strong sense: the functor

$$\begin{array}{ccc} \infty\text{-Cat}_{\text{Can}} & \rightarrow & \infty\text{-Cat}_{\text{Coind}}^{+\infty} \\ C & \mapsto & C^\circ \end{array}$$

where $C^\circ$ is the minimal marking (i.e., only the identity arrows are marked) defined in Example 2.16, is a left Quillen equivalence. Its right adjoint (the

7