104 Case studies

**Set truncation** The propositional truncation sits at the bottom of a tower of truncation operators that cut off the higher structure of a type at some dimensionality. Where the propositional truncation identifies all *points* of a type, the *set truncation* collapses all *paths* between each pair of elements in a type [Uni13, §6.9]. We can express the set truncation by the following specification.

$A : \cup \gg \textbf{inductive} \|A\|_0 \textbf{ where}$
$\mid \mathrm{pt}_0(a : A) \in \|A\|_0$
$\mid \mathrm{squash}_0(t, t') : \|A\|_0, p, p' : \mathrm{Path}(\|A\|_0, t, t'), x : \mathbb{I}, y : \mathbb{I}) \in \|A\|_0$
$[x \equiv 0 \hookrightarrow p\, y \mid x \equiv 1 \hookrightarrow p'\, y \mid y \equiv 0 \hookrightarrow t \mid y \equiv 1 \hookrightarrow t']$

The constructor $\mathrm{squash}_0$ is our first example of a 2-dimensional constructor. Given two paths, it creates a higher path (*i.e.*, square) identifying them: abstracting, we have $\lambda^\mathbb{I}\, y$. $\mathrm{squash}_0(t, t', p, p', 0, y) = p \in \mathrm{Path}(\|A\|_0, t, t')$ and $\lambda^\mathbb{I}\, y$. $\mathrm{squash}_0(t, t', p, p', 1, y) = p' \in \mathrm{Path}(\|A\|_0, t, t')$. The cubical notation for specifying boundaries generalizes gracefully to the greater-than-one-dimensional case.

Note that the arguments of $\mathrm{squash}_0$ now draw not only from the *elements* of the type being defined, but from its *path types*. In particular, supporting this specification requires that we allow dependencies between recursive arguments—here, the dependency in the types of $p$ and $p'$ on $t$ and $t'$. This is atypical in a schema for indexed inductive types, where recursive arguments are usually completely independent of each other. (Dependency among recursive arguments does, however, arise in schemata for inductive-inductive and inductive-recursive types.) We must also be able to apply the path arguments $p$ and $p'$ to interval terms (here $y$) in order to specify the boundary of the $\mathrm{squash}_0$ constructor.

**General truncation** The propositional truncation and set truncation are also known as the $(-1)$-truncation and $0$-truncation respectively; more generally, the $n$-truncation trivializes the structure of a type above dimension $n$. We could continue defining individual $n$-truncations using $n$-dimensional constructors, but many applications require that we have a single, parameterized definition of $n$-truncation uniformly in $n : \mathrm{Nat}$.

The HoTT Book proposes a fairly direct general definition of $n$-truncation using what is called a *hub-and-spoke construction* [Uni13, §6.7]. This definition relies on our ability to construct $n$-sphere types uniformly in $n : \mathrm{Nat}$, generalizing the circle (*i.e.*, 1-sphere) we saw in Chapter 4, by iteratively applying a *suspension* construction.

$A : \cup \gg \textbf{inductive} \mathrm{Susp}(A) \textbf{ where}$
$\mid \mathrm{north} \in \mathrm{Susp}(A)$
$\mid \mathrm{south} \in \mathrm{Susp}(A)$
$\mid \mathrm{merid}(a : A, x : \mathbb{I}) \in \mathrm{Susp}(A) \quad [x \equiv 0 \hookrightarrow \mathrm{north} \mid x \equiv 1 \hookrightarrow \mathrm{south}]$