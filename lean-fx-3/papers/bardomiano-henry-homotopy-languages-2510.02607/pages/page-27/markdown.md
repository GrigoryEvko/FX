The two maps $p_1, p_2 : PX \to X$ are trivial fibrations (they are both fibrations and weak equivalences), $v_1 = p_1 \circ h$ and $v_2 = p_2 \circ h$. By the observation above, we have:

$$\begin{array}{rcl} & X & \vdash & \phi(v_1) \\ \Leftrightarrow & X & \vdash & \phi(p_1 h) \\ \Leftrightarrow & PX & \vdash & \phi(h) \\ \Leftrightarrow & X & \vdash & \phi(p_2 h) \\ \Leftrightarrow & X & \vdash & \phi(v_2) \end{array}$$

This concludes the proof of the $1^{st}$ invariance theorem.

Next, we observe it is enough to prove the second invariance theorem when $X$ and $Y$ are both bifibrant. Indeed, starting from $f : X \to Y$ a weak equivalence between fibrant objects, $v : c \to X$ and $\phi \in \mathbb{L}_\lambda^M(c)$ as in the theorem. We can replace both $X$ and $Y$ by bifibrant objects

$$\begin{array}{ccc} X^{\text{COF}} & \xrightarrow[f]{\sim} & Y^{\text{COF}} \\ \downarrow\searrow & & \downarrow\searrow \\ X & \xrightarrow[f]{} & Y. \end{array}$$

First replacing $X$ by a cofibrant object $X^{\text{COF}}$ and then factoring the map $X^{\text{COF}} \to Y$, which is a weak equivalence, as a trivial cofibration followed by a trivial fibration. The map $v : c \to X$, can be lifted to a map $v' : c \to X^{\text{COF}}$. As we can already apply the $2^{nd}$ invariance theorem to trivial fibrations, we have that:

$$\begin{array}{l} X \vdash \phi(v) \Leftrightarrow X^{\text{COF}} \vdash \phi(v') \\ Y \vdash \phi(fv) \Leftrightarrow Y^{\text{COF}} \vdash \phi(f'v'). \end{array}$$

Therefore, it is enough to show the $2^{nd}$ invariance theorem for bifibrant objects.

This last step is achieved essentially using a “Brown factorization”: any weak equivalence between bifibrant objects can be factored as a section of a trivial fibration followed by a trivial fibration. Indeed, if $f : X \to Y$ is a

27