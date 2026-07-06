E. Cavallo and C. Sattler

21

▶ Component 61 (S, suspension). Over an environment with A A': Ty and a 1-to-1 correspondence $\bar{A}: (A, A') \to Ty$, we must construct a 1-to-1 correspondence between $FSusp(A)$ and $GSusp(A')$; we take $Graph(map(fwd_{\bar{A}}))$. We interpret north and south by the reflexive identities $map(fwd_{\bar{A}})(north) \asymp north$ and $map(fwd_{\bar{A}})(south) \asymp south$.

To interpret merid applied to a : A, a' : A', and $\bar{a} : \bar{A}(a, a')$, we first convert the path $\text{cong}_{\text{map}(fwd_{\bar{A}})}(Fmerid(a)) \sim Gmerid(fwd_{\bar{A}}(a))$ to an identity, then rewrite along the identity $fwd_{\bar{A}}(a) \asymp a'$ obtained from $\bar{a}$ to get an identity $\text{cong}_{\text{map}(fwd_{\bar{A}})}(Fmerid(a)) \asymp Gmerid(a')$. Using $M\lambda^{\overline{i}}$, we convert this to an M-path in the necessary identity type.

Now we interpret the eliminator. Over the environment

$$(A : Ty, C : Susp(A) \to Ty, n : C(north), s : C(south), m : (a : A) \to Path(\langle i \rangle C(merid(a) @ i), n, s))$$

we have a type

$$D := \Sigma f : (\Pi t : Susp(A).C(t)). \Sigma p_n : f(north) \sim n. \Sigma p_s : f(south) \sim s.$$
$$Path(\langle j \rangle Path(\langle i \rangle C(merid(a) @ i), p_n @ j, p_s @ j), (\lambda i.f(merid(a) @ i)), m)$$

of dependent functions into C defined on the constructors north, south, and merid by n, s, and m respectively, up to homotopy. By virtue of the eliminator, D is contractible, as are FD and GD. Thus every pair of elements from FD and GD is related in SD, in particular the pair obtained from Felim and Gelim. This gives us an almost-interpretation of elim: we have an eliminator that may satisfy the point constructor computation rules only up to paths.

We then correct our almost-interpretation on the point constructors. To interpret the eliminator, we are given type families C and C' and, over $(t : FSusp(A), t' : GSusp(A'), \bar{t} : map(fwd_{\bar{A}})(t) \asymp t')$, 1-to-1 correspondences $\bar{C}(t, t', \bar{t}) : (C(t), C'(t')) \to Ty$. We want to relate $Felim(C, n, s, m, t)$ and $Gelim(C', n', s', m', t')$ in $\bar{C}(t, t', \bar{t})$ for all related inputs. We go by $FSusp$-elimination from t and identity elimination from $\bar{t}$. For the point cases $t = Fnorth$ and $t = Fsouth$, we choose the values that the point computation rules require. For the Fmerid case, we apply the almost-eliminator to the input data to get a section of $\bar{C}$, evaluate it at the corresponding meridian, then coerce the result along the almost-eliminator's point computation paths to get a path of the correct type.

This completes the definition of $S_G^F: \mathbb{C}TT[\iota\Phi] \to Span(\mathbb{C}TT[\iota\Psi])$. In summary:

▶ Theorem 62. Let $F, G: \mathbb{C}TT[\iota\Phi] \to \mathbb{C}TT[\iota\Psi]$ in the coslice under $\text{MLTT}_{\Sigma, Id, U} + \mathbb{C}OF$. There is a $S_G^F: \mathbb{C}TT[\iota\Phi] \to Span(\mathbb{C}TT[\iota\Psi])$ in $\text{MLTT}_{\Sigma, Id}/\text{RMC}$ such that $\pi_0 S_G^F \cong F$ and $\pi_1 S_G^F \cong G$.

## 6 Conservativity

▶ Proposition 63 (2-out-of-6). Weak equivalences of democratic models of $\text{MLTT}_{\Sigma, Id}$ are closed under 2-out-of-6. That is, given morphisms of democratic models of $\text{MLTT}_{\Sigma, Id}$ $\mathcal{M} \xrightarrow{\mathcal{F}} \mathcal{N} \xrightarrow{\mathcal{G}} \mathcal{O} \xrightarrow{\mathcal{H}} \mathcal{P}$ where $\mathcal{GF}$ and $\mathcal{HG}$ are weak equivalences, the maps $\mathcal{F}$, $\mathcal{G}$, $\mathcal{H}$, and the composite $\mathcal{HGF}$ are weak equivalences.

Proof. See Kapulkin and Lumsdaine [22, Corollary 3.4].

A corollary of 2-out-of-6 is 2-out-of-3: given composable morphisms $\mathcal{G}$ and $\mathcal{F}$ between democratic models of $\text{MLTT}_{\Sigma, Id}$, if two of the three morphisms $\mathcal{F}$, $\mathcal{G}$, and $\mathcal{GF}$ are weak equivalences, then so is the third.

▶ Theorem 64. For $F: \mathbb{C}TT[\iota\Phi] \to \mathbb{C}TT[\iota\Psi]$ and $G: \mathbb{C}TT[\iota\Psi] \to \mathbb{C}TT[\iota\Phi]$ in the coslice under $\text{MLTT}_{\Sigma, Id} + \mathbb{C}OF$, the induced morphisms $\mathbf{0}_F: \mathbf{0}_{\mathbb{C}TT[\iota\Phi]} \to \mathbf{0}_{\mathbb{C}TT[\iota\Psi]}$ and $\mathbf{0}_G: \mathbf{0}_{\mathbb{C}TT[\iota\Psi]} \to \mathbf{0}_{\mathbb{C}TT[\iota\Phi]}$ are weak equivalences.