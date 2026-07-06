5.2. CARTESIAN FIBRATIONS

and the corresponding right cartesian fibration is the slice of $D$ over $a$

$$D_{/a} \to D.$$

**5.2.1.20.** Let $p : X \to Y$ be a morphism between $(\infty, \omega)$-categories. A marked 1-cell $v : x \to x'$ is *left cancellable* if for any $y$, the following natural square is cartesian:

$$\begin{array}{ccc} \hom_X(x', y) & \xrightarrow{v_!} & \hom_X(x, y) \\ \downarrow & & \downarrow \\ \hom_Y(px', py) & \xrightarrow{p(v)_!} & \hom_Y(px, py) \end{array}$$

Conversely, a 1-cell $v : y \to y'$ is *right cancellable* if for any $x$, the following natural square is cartesian:

$$\begin{array}{ccc} \hom_X(x, y) & \xrightarrow{v_!} & \hom_X(x, y') \\ \downarrow & & \downarrow \\ \hom_Y(px, py) & \xrightarrow{p(v)_!} & \hom_Y(px, py') \end{array}$$

**Lemma 5.2.1.21.** *Let $p$ be a morphism. The following conditions are equivalent:*

- (1) $p$ has the unique right lifting property against $\{0\} \to [1]^\sharp$ and marked 1-cells are left cancellable.
- (2) $p$ has the unique right lifting property against $[a, 1] \xrightarrow{\nabla} [1]^\sharp \vee [a, 1]$ for any object $a$ of $t\Theta$.
- (3) $p$ has the unique right lifting property against $[a, 1] \xrightarrow{\nabla} [1]^\sharp \vee [a, 1]$ and $[1]^\sharp \xrightarrow{\nabla} [1]^\sharp \vee [1]^\sharp$ for any object $a$ of $t\Theta$.

*Conversely, the following are equivalent:*

- (1)' $p$ has the unique right lifting property against $\{1\} \to [1]^\sharp$ and marked 1-cells are right cancellable.
- (2)' $p$ has the unique right lifting property against $[a, 1] \xrightarrow{\nabla} [a, 1] \vee [1]^\sharp$ for any object $a$ of $t\Theta$.
- (3)' $p$ has the unique right lifting property against $[a, 1] \xrightarrow{\nabla} [a, 1] \vee [1]^\sharp$ and $[1]^\sharp \xrightarrow{\nabla} [1]^\sharp \vee [1]^\sharp$ for any object $a$ of $t\Theta$.

265