1:22

M. SHULMAN

Vol. 19:2

linear exponential comonad !. Therefore, it gives rise to an LNL adjunction $\mathcal{M} \rightleftarrows \mathcal{L}$ as above, where $\mathcal{M}$ is the Eilenberg–Moore category of the comonad !. Hence, by Proposition 3.15, any subcategory of this $\mathcal{M}$ (such as the Kleisli category) yields an LNL polycategory $\mathcal{P}$ with $\mathcal{P}^{\mathrm{L}} = \mathcal{L}$ and having $\otimes, \mathbb{1}, \mathfrak{A}, \bot, \mathsf{F}, \mathsf{U}$. Similarly, any subcategory of the opposite of the Eilenberg–Moore category of the monad ? yields an LNL polycategory $\mathcal{P}$ with $\mathcal{P}^{\mathrm{L}} = \mathcal{L}$ and having $\otimes, \mathbb{1}, \mathfrak{A}, \bot, \mathsf{F}, \mathsf{U}$.

If $\mathcal{L}$ has duals, hence is $*$-autonomous, then by [BCS96, Proposition 5.1] the modalities ! and ? are dual, in that $?A \cong (!(A^*))^*$. This implies that their Eilenberg–Moore and Kleisli categories are dual to each other, by equivalences that lie over the self-duality $(\cdot)^*$; hence these two LNL polycategories coincide and are a $*$-autonomous LNL adjunction that induces the given ! and ?. However, if $\mathcal{L}$ does not have duals, then the Eilenberg–Moore categories of ! and ? need not be dual:

**Example 3.17.** Let $\mathcal{L}$ be a distributive lattice that is not a Boolean algebra. As in [CS97], we can regard $\mathcal{L}$ as a linearly distributive category with $\otimes = \wedge$ and $\mathfrak{A} = \vee$. Since $\wedge$ is the cartesian product and $\vee$ the cartesian coproduct, we can equip $\mathcal{L}$ with storage modalities ! and ? that are both just the identity. (Thanks to Robin Cockett for pointing out this example.) The Eilenberg–Moore categories of this ! and ? are then both just $\mathcal{L}$ itself, which may not be self-dual.

In fact this $\mathcal{L}$ cannot occur as $\mathcal{P}^{\mathrm{L}}$ for *any* LNL polycategory $\mathcal{P}$ with $\mathsf{F}, \mathsf{U}, \mathsf{F}, \mathsf{U}$ such that its (identity) modalities ! and ? are recovered as $\mathsf{FU}$ and $\mathsf{FU}$ respectively. To see this, note that for any nonlinear object $X$ in an LNL polycategory, if $\mathsf{FX}$ and $\mathsf{FX}$ both exist, then they are dual to each other. Thus, if $\mathsf{F}, \mathsf{F}$ both exist, then any object of the form $\mathsf{FX}$ or $\mathsf{FX}$ has a dual — and hence if $! = \mathsf{FU}$ is the identity, then *every* object has a dual. But this would imply that $\mathcal{L}$ is a Boolean algebra.

Thus, if we want to embed a general linearly distributive category with storage into an LNL polycategory, we have to give up on having all $\mathsf{F}, \mathsf{U}, \mathsf{F}, \mathsf{U}$. But we can get away with something slightly less:

**Proposition 3.18.** *A linearly distributive category $\mathcal{L}$ admits storage modalities if and only if it can occur as $\mathcal{P}^{\mathrm{L}}$ for an LNL polycategory $\mathcal{P}$ having $\otimes, \mathbb{1}, \mathfrak{A}, \bot, \mathsf{U}, \mathsf{U}$ along with $\mathsf{F}$ defined on the image of $\mathsf{U}$ and $\mathsf{F}$ defined on the image of $\mathsf{U}$.*

*Proof.* For “if”, just note that the proof of Proposition 3.16 uses only this weaker hypothesis. For “only if”, let $\mathcal{L}$ be a symmetric linearly distributive category with storage, and define an LNL polycategory $\mathcal{L}_{!,?}$ as follows. Its linear objects are the objects of $\mathcal{L}$, while its nonlinear objects consist of two copies of the objects of $\mathcal{L}$ denoted $A^!$ and $A^?$. Its homsets are defined by:

$$\begin{aligned} \mathcal{L}_{!,?}(A^!, \dots, A^!, p, B^?, \dots, B^?_q \mid C_1, \dots, C_m; D_1, \dots, D_n) \\ = \mathcal{L}(!A_1 \otimes \dots \otimes !A_p \otimes C_1 \otimes \dots \otimes C_m, ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} D_1 \mathfrak{A} \dots \mathfrak{A} D_n) \\ \mathcal{L}_{!,?}(A^!, \dots, A^!, p, B^?, \dots, B^?_q; C!) = \mathcal{L}(!A_1 \otimes \dots \otimes !A_p, ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q \mathfrak{A} C) \\ \mathcal{L}_{!,?}(A^!, \dots, A^!, p, B^?, \dots, B^?_q; C^?) = \mathcal{L}(!A_1 \otimes \dots \otimes !A_p \otimes C, ?B_1 \mathfrak{A} \dots \mathfrak{A} ?B_q) \end{aligned}$$

In particular, we have

$$\begin{aligned} \mathcal{L}_{!,?}(A^!; C!) &= \mathcal{L}(!A, C) & \mathcal{L}_{!,?}(A^!; C^?) &= \mathcal{L}(!A \otimes C, \bot) \\ \mathcal{L}_{!,?}(B^?; C^?) &= \mathcal{L}(C, ?B) & \mathcal{L}_{!,?}(B^?; C!) &= \mathcal{L}(\mathbb{1}, ?B \mathfrak{A} C). \end{aligned}$$