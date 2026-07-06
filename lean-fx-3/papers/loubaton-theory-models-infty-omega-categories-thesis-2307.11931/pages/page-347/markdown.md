6.2. YONEDA LEMMA AND APPLICATIONS

Eventually, using the canonical equivalence between $[a, 1] \times [b, 1]$ and the colimit of the span

$$[a, 1] \vee [b, 1] \leftarrow [a \times b, 1] \rightarrow [b, 1] \vee [a, 1],$$

the $\infty$-groupoid $\operatorname{Hom}([a, 1] \times [b, 1], C)_f$ fits in a cartesian square:

$$\begin{array}{c} \operatorname{Hom}([a, 1] \times [b, 1], C)_f \longrightarrow \operatorname{Hom}(b, \operatorname{hom}(f(0, 0), f(0, 1))) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \operatorname{Hom}(b, \operatorname{hom}(f(1, 0), f(1, 1))) \longrightarrow \operatorname{Hom}(a \times b, \operatorname{hom}(f(0, 0), f(1, 1))) \end{array}$$

As all these objects are $\mathbf{U}$-small by assumption, this concludes the proof.

**6.2.1.4.** Let $C$ be an $(\infty, \omega)$-category $C$. We define the simplicial object $S(\mathrm{N}_{(\omega, 1)} C)$ by the formula

$$S(\mathrm{N}_{(\omega, 1)} C)_n := \coprod_{x_0, \dots, x_n : A_0} \coprod_{y_0, \dots, y_n : A_0} \operatorname{hom}_C(x_n, \dots, x_0, y_0, \dots, y_n)$$

This object comes along with a canonical projection

$$S(\mathrm{N}_{(\omega, 1)} C) \rightarrow \mathrm{N}_{(\omega, 1)} C^t \times \mathrm{N}_{(\omega, 1)} C. \tag{6.2.1.5}$$

which obviously is a left fibration. As this construction if functorial, it induces a functor:

$$\begin{array}{l} (\infty, \omega)\text{-cat} \rightarrow \operatorname{Arr}((\infty, \omega, 1)\text{-cat}) \\ C \mapsto (S(\mathrm{N}_{(\omega, 1)} C) \rightarrow \mathrm{N}_{(\omega, 1)} C^t \times \mathrm{N}_{(\omega, 1)} C) \end{array}$$

**6.2.1.6.** Through this section, we fix a locally $\mathbf{U}$-small $(\infty, \omega)$-category $C$. The left fibration (6.2.1.5) is then $\mathbf{U}$-small, and by definition of $\underline{\omega}$, this induces a morphism

$$\operatorname{hom}_C(\_, \_): C^t \times C \rightarrow \underline{\omega} \tag{6.2.1.7}$$

Using the canonical equivalence

$$\mathbf{F} h_{(x, y)}^{C^t \times C} \sim \mathbf{F} h_x^{C^t} \times \mathbf{F} h_y^C$$

the corresponding left cartesian fibration is then the colimit of a simplicial object whose value on $n$ is given by:

$$\coprod_{x_0, \dots, x_n} \coprod_{y_0, \dots, y_n} \mathbf{F} h_{x_n}^{C^t} \times \operatorname{hom}_C(x_n, \dots, x_0, y_0, \dots, y_n)^b \times \mathbf{F} h_{y_n}^C$$

337