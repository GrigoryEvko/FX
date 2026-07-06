morphism. The second condition is that there is an object $G_1$ that, in a sense, classifies isomorphisms between points of the stacks.

The proof is then completed by checking the two conditions for the case $X \mapsto \mathbf{KHaus}_X$. Checking the first requires us to recall that every compact Hausdorff locale is the completion of a normal distributive lattice (NDL). We use this to show how any compact Hausdorff locale can be pulled back (via a cover) to a stage at which it is the completion of the pullback of the generic NDL. (This generic NDL exists because the theory of normal distributive lattices is geometric, and we are able to obtain the compact Hausdorff locale needed as the completion process commutes with pullback functors determined by geometric morphisms.) Constructing the “isomorphisms classifier” $G_1$ required for the second condition is reasonably straightforward using the generic compact Hausdorff locale defined via the completion of the generic normal distributive lattice. This is because compact Hausdorff locales are locally compact and so are exponentiable.

We finish by including some comments on how to extend the result to arbitrary morphisms between compact Hausdorff locales, showing how to represent these as $\mathbb{S}$-homotopies using the main result of [HT22].

## 2 Background and preliminary material

### 2.1 Locales

For background on locales consult Part C of [J02]. We will pass through the equivalence $\mathbf{Loc}/X \simeq \mathbf{Loc}_{Sh(X)}$, e.g. C1.6.3 of [J02], without comment. We assume familiarity with the notion of proper and open locale map; a locale $X$ is discrete(compact Hausdorff) if and only if all finite (including nullary) diagonals are open(proper).

Open and proper locale maps are pullback stable, and if they are also surjections then they are effective descent morphisms in the category of locales $\mathbf{Loc}$. A locale map $f: X \longrightarrow Y$ is *of effective descent* if the pullback functor $f^*$ is monadic; equivalently, the canonical map $\mathbf{Loc}/Y \to [\mathbb{X}_f, \mathbf{Loc}]$ is an equivalence, where $\mathbb{X}_f$ is the localic groupoid determined by the kernel pair of $f$ (we use the notation $[\mathbb{G}, \mathbf{Loc}]$ for the category of $\mathbb{G}$-objects for any localic groupoid $\mathbb{G}$). Effective descent morphisms are pullback stable, essentially because monadicity criteria are pullback stable.

Open and proper maps can be isolated using lower ($P^L$) and upper ($P^U$) power locale constructions; a locale map $g: Z \longrightarrow X$ is open if and only if $P_X^L(Z_g)$ has a top element (and is proper if and only if $P_X^U(Z_g)$ has a bottom). See Theorem 4.9 (Theorem 5.10) of [V94]. Here we are following the notation that if $f: X \longrightarrow Y$ is a locale map then we write $X_f$ when considering it as an object of the slice $\mathbf{Loc}/Y$.

2