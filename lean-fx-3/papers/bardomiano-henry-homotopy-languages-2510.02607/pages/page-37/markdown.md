When we analyze the set of generating cofibrations $I$ we rediscover the generalized algebraic theory of bicategories $Bicat_{=}$:

- $\mathbb{O} \to \mathbb{1} \longmapsto \vdash \mathsf{Ob}\,\mathsf{Type}$
- $\{x\} \sqcup \{y\} \xrightarrow{\sum w} \{x \to y\} \mapsto x, y : \mathsf{Ob} \vdash \mathsf{Hom}(x, y)$
- $x \xrightarrow[1]{0} y \xrightarrow{\sum w} x \xrightarrow[1]{0} y \mapsto x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y) \vdash \mathsf{Hom}(f, g)\,\mathsf{Type}$
- $x \xrightarrow[1]{0} y \xrightarrow{\sum w} x \xrightarrow[1]{0} y \mapsto \begin{cases} x, y : \mathsf{Ob}, f, g : \mathsf{Hom}(x, y), \\ \alpha, \beta : \mathsf{Hom}(f, g) \vdash \mathsf{Eq}(\alpha, \beta)\,\mathsf{Type} \end{cases}$

Moreover, we can also introduce the composition and identity operations for arrows and cells:

- Composition operation for arrows: \( x: \mathsf{Ob}, y: \mathsf{Ob}, z: \mathsf{Ob}, f: \mathsf{Hom}(x, y), g: \mathsf{Hom}(y, z) \vdash g \circ f: \mathsf{Hom}(x, z) \).
- Identity operator for arrows: \( x: \mathsf{Ob} \vdash \mathsf{id}_x: \mathsf{Hom}(x, x) \).
- Vertical composition of cells: \( x, y: \mathsf{Ob}, f, g, h: \mathsf{Hom}(x, y), \alpha: \mathsf{Hom}(f, g), \beta: \mathsf{Hom}(g, h) \vdash \beta \circ \alpha: \mathsf{Hom}(f, h) \).
- Horizontal composition of cells: \( x, y, z: \mathsf{Ob}, f, g: \mathsf{Hom}(x, y), h, k: \mathsf{Hom}(y, z), \alpha: \mathsf{Hom}(f, g), \beta: \mathsf{Hom}(h, k) \vdash \alpha * \beta: \mathsf{Hom}(h \circ f, k \circ g) \).
- Identity operator for cells: \( x, y: \mathsf{Ob}, f: \mathsf{Hom}(x, y) \vdash \mathsf{id}_f: \mathsf{Hom}(f, f) \).

One can also attempt to list all the axioms that the above theory ought to satisfy, with the risk of running out of space. We simply exemplify this with the associator:

$$
\begin{aligned}
w, x, y, z : \mathsf{Ob}, f : \mathsf{Hom}(w, x), g : \mathsf{Hom}(x, y), h : \mathsf{Hom}(y, z), \\
\alpha : \mathsf{Hom}((h \circ g) \circ f, h \circ (g \circ f)), \beta : \mathsf{Hom}((h \circ (g \circ f), h \circ g) \circ f) \\
\quad \vdash r : \mathsf{Eq}(\alpha \circ \beta, \mathsf{id}_{(h \circ (g \circ f)}) \wedge s : \mathsf{Eq}(\beta \circ \alpha, \mathsf{id}_{(h \circ g) \circ f}).
\end{aligned}
$$

We also include the axioms for Eq — the same ones as for categories — that gives us the expected behaviour.

37