270

Programming in cohesive parametric type theory

refutation of LEM$_{-}$, on the other hand, U occurs in a positive position. In sum, although we cannot decide the inhabitation of parametric types, this does not imply we cannot decide the inhabitation of the “smaller” class of pointwise types.$^{1}$

### 15.3 Bridge-discreteness

Before introducing cohesive parametric type theory, we already had a notion of discreteness: the concept of bridge-discrete type introduced in Section 10.3. These play an important role in parametricity theorems that involve external type parameters, such as the characterization of $(B : \mathrm{U}) \to (A \to B) \to B$ for bridge-discrete $A$ given in that section. We would therefore hope that pointwise types brought to the parametric fragment by Disc are bridge-discrete. This is indeed the case. (We do not, on the other hand, expect to be able to show that every bridge-discrete type is isomorphic to one of the form $\operatorname{Disc}(A)$.)

**Theorem 15.3.1.** For any $(\mathrm{cc} \mid A : \mathrm{U})$, $\operatorname{Disc}(A)$ is bridge-discrete.

*Proof.* Per Lemma 10.3.3, it suffices to show that $\operatorname{Bridge}(\operatorname{Disc}(A), d_0, d_1)$ is a retract of $\operatorname{Path}(\operatorname{Disc}(A), d_0, d_1)$ for every $d_0, d_1 : \operatorname{Disc}(A)$. We take an approach similar to our proof of boolean bridge-discreteness (Theorem 10.3.7), first defining a function into the Gel type $G_x := \operatorname{Gel}_x(\operatorname{Disc}(A), \operatorname{Disc}(A), \operatorname{Path}(\operatorname{Disc}(A), -, -))$ as follows.

$$F_x := \lambda d. \left[ \begin{array}{l} \text{case } d \text{ of} \\ | \operatorname{mod}(a) \mapsto \operatorname{gel}_x(\operatorname{mod}(a), \operatorname{mod}(a), \lambda_{-\dots}^{\mathbb{I}}. \operatorname{mod}(a)) \end{array} \right] \in \operatorname{Disc}(A) \to G_x$$

For this term to be well-typed according to Rules 14.4.13, we must show that we have $(\mathrm{cc} \mid A : \mathrm{U}), x : \mathrm{I}, (\mathrm{cc} \mid a : A) \gg \operatorname{gel}_x(\operatorname{mod}(a), \operatorname{mod}(a), \lambda_{-\dots}^{\mathbb{I}}. \operatorname{mod}(a)) \in G_x$ @ par. We want to apply Gel introduction and Disc introduction in each argument. Looking at the first, we then need $((\mathrm{cc} \mid A : \mathrm{U}), x : \mathrm{I}, (\mathrm{cc} \mid a : A) \setminus x).\mathrm{cc} \gg a \in A$ @ pt. This follows by computing the effect of restriction and connected components on the context: we have $((\mathrm{cc} \mid A : \mathrm{U}), x : \mathrm{I}, (\mathrm{cc} \mid a : A) \setminus x).\mathrm{cc} = A : \mathrm{U}, a : A$. The same argument allows us to type the other two arguments. The key here is that we can guarantee $a$ is apart from the interval variable $x$, because it is hypothesized under cc: it only depends on the connected components of its predecessors in the context. Using $F_x$, we obtain a function from bridges in $\operatorname{Disc}(A)$ to paths in $\operatorname{Disc}(A)$.

$$F := \lambda p. \operatorname{ungel}(x.F_x(p x)) \in \operatorname{Bridge}(\operatorname{Disc}(A), d_0, d_1) \to \operatorname{Path}(\operatorname{Disc}(A), F_0 d_0, F_1 d_1)$$

$^{1}$The pointwise excluded middle may of course fail for other reasons. Sattler has claimed that LEM$_{-1}$ is in fact falsified in the Kan cartesian cubical set model of type theory [Sat18], a fact that would presumably carry over to our computational interpretation.