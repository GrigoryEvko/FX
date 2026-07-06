16:12

A. NUYTS AND D. DEVRIESE

Vol. 20:2

element. Thus we see that the transpension type essentially consists of one meridian $(i : \mathbb{I}) \to [i]T$ for every $t : T$, and that these meridians are all equal to $\mathsf{pole}_0$ at $i = 0$ and analogously to $\mathsf{pole}_1$ at $i = 1$. This makes the transpension type quite reminiscent of a dependent version of the suspension type from HoTT [Uni13], although the quantification of the context in the formation and construction rules is obviously a distinction.

2.3. **Internal transposition.** We can internally show that the following types are isomorphic:$^7$

$$(\forall(u : \mathbb{U}).A) \to B \cong \forall(u : \mathbb{U}).(A \to [u]B).$$

Indeed, given $f : (\forall(u : \mathbb{U}).A) \to B$, we can define $g : \forall(u : \mathbb{U}).(A \to [u]B)$ by

$$g\,u\,a = \mathsf{mer}[u](f(\lambda u.a)).$$

Conversely, given $g : \forall(u : \mathbb{U}).(A \to [u]B)$, we can define $f : (\forall(u : \mathbb{U}).A) \to B$ by

$$f\,\hat{a} = \mathsf{unmer}(u.g\,u\,(\hat{a}\,u)).$$

These constructions are mutually inverse. Indeed, plugging the definition of $f$ into that of $g$, we find in context $(\Gamma, u : \mathbb{U}, a : A)$:

$$\mathsf{mer}[u]\,(\mathsf{unmer}(u.g\,u\,(\lambda u.a)\,u))) = \mathsf{mer}[u]\,(\mathsf{unmer}(u.(g\,u\,a)[u/u,(\lambda u.(a))\,u/(a)])) = g\,u\,a$$

using the $\eta$-rule of the transpension type. Conversely, plugging $g$ into $f$, we find in context $(\Gamma, \hat{a} : \forall u.A)$:

$$\begin{aligned} &\mathsf{unmer}(u.\,(\mathsf{mer}[u]\,(f(\lambda u.a)))\,[u/u, \hat{a}\,u/a]\,) \\ &= \mathsf{unmer}(u.(\mathsf{mer}[u]\,(\,(f(\lambda u.a))[\lambda u.(\hat{a}\,u)/\lambda u.(a)]\,))) \quad \text{(FF:TRANSP:INTRO:NAT)} \\ &= \mathsf{unmer}(u.(\mathsf{mer}[u]\,(\,(f(\lambda u.\hat{a}\,u))\,))) \quad \text{(Corollary 2.3)} \\ &= f(\lambda u.(\hat{a}\,u)) = f\,\hat{a}. \quad \text{(FF:TRANSP:BETA)} \end{aligned}$$

2.4. **Higher-dimensional pattern matching.** Now that we know internally that $\forall u$ is a left adjoint (with internal right adjoint $[u]$), we can proceed to conclude that it preserves colimits, e.g. we can show $i : (\forall u.A \uplus B) \cong (\forall u.A) \uplus (\forall u.B)$. The map to the left is trivially defined by case analysis. The map to the right is equivalent by transposition to a function $\forall u.(A \uplus B \to [u]\,(\lceil \forall v.A[v/u] \rceil) \uplus (\forall v.B[v/u]\,)))$. This is in turn constructed by case analysis from the transpositions of the coproduct's constructors $\mathsf{inl}$ and $\mathsf{inr}$.

By straightforward application of Section 2.3, the transpositions of the constructors are:

$$\lambda u.\lambda a.\mathsf{mer}[u]\,(\mathsf{inl}\,(\lambda u.a)) : \forall u.(A \to [u]\,(\lceil \forall v.A[v/u] \rceil) \uplus (\forall v.B[v/u]\,)))$$

$$\lambda u.\lambda b.\mathsf{mer}[u]\,(\mathsf{inr}\,(\lambda u.b)) : \forall u.(B \to [u]\,(\lceil \forall v.A[v/u] \rceil) \uplus (\forall v.B[v/u]\,)))$$

Pasting these together, we get

$$\begin{aligned} \lambda u.\lambda c.\mathsf{case}\,c\,\mathsf{of} &\left\{\begin{array}{ll} \mathsf{inl}\,a & \mapsto \mathsf{mer}[u]\,(\mathsf{inl}\,(\lambda u.a)) \\ \mathsf{inr}\,b & \mapsto \mathsf{mer}[u]\,(\mathsf{inr}\,(\lambda u.b)) \end{array}\right\} \\ &: \forall u.(A \uplus B \to [u]\,(\lceil \forall v.A[v/u] \rceil) \uplus (\forall v.B[v/u]\,))). \end{aligned}$$

Transposing again as in Section 2.3, we find

$$i : (\forall u.A \uplus B) \to (\forall u.A) \uplus (\forall u.B)$$

$^7$This statement of internal transposition is not parallel to the general MTT one (Proposition 3.4). The current variation is provable from the general result because the right adjoint $[u]$ is fully faithful.