Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:23

That is, the category of nonlinear objects and unary morphisms consists of a copy of the Kleisli category of ! (the objects $A^!$) and a copy of the opposite of the Kleisli category of ? (the objects $B^?$), with the morphisms between the two defined in a twisted way using the linearly distributive structure.

Composition of two linear morphisms is defined just as in the ordinary symmetric polycategory underlying $\mathcal{L}$. To compose a nonlinear morphism with either a linear or nonlinear morphism, we make use of the “generalized Kleisli lift”: given

$$f : !A_1 \otimes \dots \otimes !A_p \longrightarrow ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} C$$

we can construct the composite

$$\begin{array}{l} !A_1 \otimes \dots \otimes !A_p \rightarrow !!A_1 \otimes \dots \otimes !!A_p \\ \quad \rightarrow !(!A_1 \otimes \dots \otimes !A_p) \\ \quad \xrightarrow{!}f \quad !(?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} C) \\ \quad \rightarrow ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} !C \end{array}$$

where the first map is composed of the comultiplications $!A_i \to !!A_i$ of !, the second map is the lax monoidal structure of !, the third in $!f$, and the fourth is $q$ applications of the strength $!(?B \mathfrak{A} C) \to ?B \mathfrak{A} !C$. By first applying this construction to a nonlinear morphism with codomain $C^!$, or the dual construction to one with codomain $C^?$, we can then compose it along this object with any other morphism as usual in the underlying polycategory of $\mathcal{L}$.

Of course this LNL polycategory has $\otimes, \mathbb{1}, \mathfrak{A}, \bot$. By construction it has $\cup A = A^!$ and $\cap A = A^?$, and partially defined $\mathsf{F}A^! = !A$ and $\bot A^? = ?A$. Note that this is very similar to the proof in [BCS96, §3.2] that proof nets with storage are sound for linearly distributive categories with storage.

This “double Kleisli category” construction is functorial, and lands inside the slice category LNLPoly/DBLSPLIT from Remark 2.7. In terms of this slice, we can describe the restricted domains of $\mathsf{F}$ and $\bot$ by saying that $\mathsf{F}$ is defined on left-hand objects and $\bot$ on right-hand ones.

Moreover, if $\mathcal{L}$ is $*$-autonomous, then $A^? \cong (A^*)^!$ in $(\mathcal{L}_{!,?})^{\mathrm{NL}}$. Thus in this case $\mathcal{L}_{!,?}$ is equivalent (though not isomorphic) to the Kleisli adjunction of ! and also to the Kleisli adjunction of ?.

This gives us the following locally full sub-2-categories of LNLPoly:

- Linearly distributive categories with storage.
- $*$-autonomous categories with storage.
- Linearly distributive or $*$-autonomous categories with storage, any desired colimits preserved by the tensor product in each variable, and any desired limits preserved by the cotensor product in each variable.

# 4. UNIFYING UNIVERSALITY

In defining LNL doctrines, we will want to work generally with classes of universal arrows and colimits in LNL polycategories. Unfortunately, the different kinds of objects and morphisms in an LNL polycategory make such a general treatment quite cumbersome. For instance, we already saw in Section 2 that there are formally five different kinds of “universal morphism” in an LNL polycategory, which has the consequence that a fully formal proof