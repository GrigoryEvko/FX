Truncations 105

If we take the type Circle defined in Chapter 4 and apply the suspension, we get a type Susp(Circle) with two “poles” (north and south) and a “line of longitude” (merid) from pole to pole for every “point on the equator” (element of the circle). This type is the 2-sphere. Iterating the suspension construction produces the $n$-spheres for every $n$. Actually, we can start this definition from $-1$, defining Sphere($-1$) := Void and Sphere($n+1$) := Susp(Sphere($n$)) for $n \geq -1$; the type Susp(Void) is isomorphic to Bool, and Susp(Bool) to Circle.

Given a type $A$, a map $F \in \text{Sphere}(0) \rightarrow A$ picks out two points in $A$, namely $F$ north and $F$ south. A map $F \in \text{Sphere}(1) \rightarrow A$ picks out two points and two paths in $A$ between them: $F$ north, $F$ south, $\lambda^\perp x \cdot F$ (merid(north, $x$)), and $\lambda^\perp x \cdot F$ (merid(south, $x$)). These collections of data are exactly the inputs to the squash and squash$_0$ constructors respectively, which inspires the following general definition of $n$-truncation.

$$
\begin{aligned}
& n : \text{Nat}, A : \cup \gg \textbf{inductive} \|A\|_n \textbf{ where} \\
& | \text{pt}_n(a : A) \in \|A\|_n \\
& | \text{hub}_n(f : \text{Sphere}(n) \rightarrow \|A\|_n) \in \|A\|_n \\
& | \text{spoke}_n(f : \text{Sphere}(n) \rightarrow \|A\|_n, s : \text{Sphere}(n), x : \mathbb{I}) \in \|A\|_n \\
& [x \equiv 0 \hookrightarrow \text{hub}_n(f) \mid x \equiv 1 \hookrightarrow f s]
\end{aligned}
$$

For each diagram to be squashed, *i.e.*, map Sphere($n$) $\rightarrow \|A\|_n$, the $n$-truncation type adds a point hub$_n(f)$ and draws a path $\lambda^\perp x \cdot \text{spoke}_n(f, s, x)$ from the hub to each element $f$ $s$ of the diagram, thus filling it in.

From a schema design perspective, the notable feature of this specification is its use of recursive arguments of function type—in this case, maps from Sphere($n$) into the type being constructed—and likewise the application of these in the definition of the boundary, paralleling the use of paths in our previous definition of $\|A\|_0$. Such recursive arguments are called *generalized recursive arguments* in Dybjer’s schema for (non-higher) indexed inductive types [Dyb94].

Note that not all function types involving the type being defined should be permissible in an inductive definition. For example, the existence of a type inductively defined by the following specification is contradictory.

$$
\begin{aligned}
& \textbf{inductive } \mathbf{X} \textbf{ where} \\
& | \text{fold}(f : \mathbf{X} \rightarrow \text{Bool}) \in \mathbf{X}
\end{aligned}
$$

The non-existence of this type can be blamed on the fact that $\mathbf{X}$ occurs *negatively* in the arguments to fold, that is, in the domain of a function type. Thus, for one, the existence of a fixed point is not guaranteed by theorems such as Theorem 2.1.20 that rely on monotonicity. Following the standard approaches for inductive type schemata, therefore, we will restrict recursive argument types to a *strictly positive* grammar, only allowing the type being defined to occur in the codomain of function types. Note that the