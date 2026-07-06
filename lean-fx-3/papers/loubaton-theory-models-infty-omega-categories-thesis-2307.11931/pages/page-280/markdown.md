CHAPTER 5. THE $(\infty, 1)$-CATEGORY OF MARKED $(\infty, \omega)$-CATEGORIES

Applying the functor $\hom_(\_, \_)$ we get the following pullback diagram:

$$\begin{array}{ccc} \hom_{X''}(x, y) & \longrightarrow & \hom_{X'}(x, y) & \longrightarrow & \hom_X(x, y) \\ \tilde{p}'' \downarrow & & \tilde{p}' \downarrow & & \tilde{p} \downarrow \\ b & \xrightarrow{i} & a & \longrightarrow & \hom_Y(px, py) \end{array}$$

and the dual version of proposition 5.1.4.9 implies that $\tilde{p}'' \to \tilde{p}'$ is a left Gray deformation retract. As this is true for any $i : b \to a$ in $I_g$, for any object of $X$, and any $a \to \hom_Y(px, py)$, this implies that $\hom_X(x, y) \to \hom_Y(px, py)$ fulfills condition (3)'. As mentioned above, an obvious induction induces (3) $\Rightarrow$ (4). We show similarly (3)' $\Rightarrow$ (4)'.

Now let's show (4) $\Rightarrow$ (1) and (4)' $\Rightarrow$ (1)'. We show by induction on $n$ that for any element $a$ of $t\,G_n := \{\mathbf{D}_k\}_{0 \leq k \leq n} \cup \{(\mathbf{D}_k)_l\}_{1 \leq k \leq n}$, if $p$ fulfills (4) (resp. (4)') $p$ has the unique right lifting property against $a \otimes \{0\} \to a \otimes [1]^\sharp$ (against $a \otimes \{1\} \to a \otimes [1]^\sharp$).

Suppose then that this is true at the stage $n$, and suppose that $p$ fulfills (4). Let $a$ be an object of $t\,G_n$. Remark that according to the equation (5.1.3.9), $[a, 1] \otimes \{0\} \to [a, 1] \otimes [1]^\sharp$ fits in the sequence of pushouts

$$\begin{array}{ccc} [0] & \xrightarrow{i_0^+} & [a, 1] \otimes \{0\} \\ \downarrow_{i_0} & & \downarrow \\ [1]^\sharp & \longrightarrow & [a, 1] \vee [1]^\sharp \longleftarrow [a \otimes \{1\}, 1] \\ & & \downarrow \searrow \downarrow \\ [a, 1] & \longrightarrow & [a, 1] \vee [1]^\sharp \cup [a \otimes [1]^\sharp, 1] \longleftarrow [a \otimes [1]^\sharp, 1] \\ \downarrow_{\nabla} & & \downarrow \\ [1]^\sharp \vee [a, 1] & \longrightarrow & [a, 1] \otimes [1]^\sharp \end{array}$$

By induction hypothesis, for any pair of objects $(x, y)$ of $X$, $\hom_X(x, y) \to \hom_Y(px, py)$ has the unique right lifting property against $a \otimes \{1\} \to a \otimes [1]^\sharp$ for $a \in t\,G_n$. Furthermore, lemma 5.2.1.21 implies that $p$ has the unique right lifting property against $\nabla : [a, 1] \to [1]^\sharp \vee [a, 1]$. The morphism $p$ then has the unique right lifting property against $[a \otimes \{1\}, 1] \to [a \otimes [1]^\sharp, 1]$ for $a \in t\,G_n$. The class of morphisms having the unique right lifting property against $p$ being closed under colimits, this implies that it includes $[a, 1] \otimes \{0\} \to [a, 1] \otimes [1]^\sharp$. To conclude, one has to show that $p$ has the unique right lifting property against $[1]^\sharp \times \{0\} \to [1]^\sharp \times [1]^\sharp$. Remark that according to proposition 5.1.1.34, $[1]^\sharp \times \{0\} \to [1]^\sharp \times [1]^\sharp$

270