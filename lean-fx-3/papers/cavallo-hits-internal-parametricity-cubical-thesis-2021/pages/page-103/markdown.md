91

type theories—Awodey and Warren’s work on modeling identity types with weak factorization systems [War08; AW09]—a guiding motivation has been their potential as a language for proving results in topology and homotopy theory. This program, labelled *synthetic homotopy theory*, took center stage in the seminal **HoTT** Book [Uni13], and has continued to expand since, even generating new classical results [FFLL16; ABFJ20].

To get a taste of the kind of topological results we can state and prove in cubical type theory, let us consider a simple HIT with non-trivial higher structure: a *circle*.

# **inductive Circle where**

| base $\in$ Circle

| loop($x : \mathbb{I}$) $\in$ Circle [$x \equiv 0 \hookrightarrow$ base | $x \equiv 1 \hookrightarrow$ base]

This circle has a single base point and a single loop at that point, that is, a path from that point to itself. One way we can analyze the circle is by characterizing the type Path(Circle, base, base) of paths from the base point to itself; this is the *fundamental group* of (Circle, base).$^{3}$ Calculating fundamental groups is one of the most basic tools for classifying spaces in algebraic topology; for example, we can see that Circle is not isomorphic to Unit or to Circle $\times$ Circle by comparing their fundamental groups.

We certainly expect there to be at least two paths from base to base: the constant path, $\lambda^{\mathbb{I}}x$. base, and the path given by the loop constructor, $\lambda^{\mathbb{I}}x$. loop($x$). In fact, because paths (like equalities) are invertible and composable, there are integer-many paths: we wind up with an isomorphism Path(Circle, base, base) $\simeq$ Int. The path that goes around the loop “forward” $n$ times corresponds to the positive integer $n$, while the path that goes around the loop “backward” $n$ times corresponds to $-n$.

We will not give a proof of this isomorphism here—see [LS13] or [Uni13, §8.1]—but we do want to call attention to one aspect. To construct the isomorphism, we must of course be able to define a function Path(Circle, base, base) $\to$ Int. That is, we must be able to *extract data* (an integer) *from a path*. Thus we arrive again at the problem at the root of effectivity of quotients. This time, with contentful equality in hand, we will be able to solve it.

**Descent and effectivity** Both the characterization of Path(Circle, base, base) and effectivity of quotients depend on a more fundamental *descent* property, a concept which originates in category theory and arises in cubical type theory from a combination of univalence and the ability to define types by case analysis.

Observe that we have an isomorphism $I \in \text{Int} \simeq \text{Int}$ whose forward map sends the integer $n$ to its successor $n + 1$. By univalence, this isomorphism induces a path in the

$^{3}$A bit more precisely, this is the *loop space*, while the fundamental group is the set truncation $\|\text{Path}(\text{Circle}, \text{base}, \text{base})\|_0$ of this type. In this case, the two are isomorphic, as the circle has no structure above dimension one.