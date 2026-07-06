74

Cubical type theory

### 3.2.2 Paths in compound types

One theoretical and practical benefit of path equality is the ease with which we can characterize the path types of compound types. We have already seen this implicitly in the previous section, where we built a path in a product type (the singleton type) from a pair of paths $\lambda^{\mathbb{I}}x$. $T_x$ and $\lambda^{\mathbb{I}}x$. $Q_x$ in the component types. That particular case is an instance of the following general principle: we have an isomorphism between paths in products and products of paths.

**Lemma 3.2.4 (Paths in products).** Let $x : \mathbb{I} \gg A$ type and $x : \mathbb{I}, a : A \gg B$ type be given together with $t_0 : ((a : A) \times B)[0/x]$ and $t_1 : ((a : A) \times B)[1/x]$. Then we have an isomorphism of the following type.

$$\operatorname{Path}(x.(a : A) \times B, t_0, t_1)$$

$$\simeq$$

$$(p : \operatorname{Path}(x.A, \operatorname{fst}(t_0), \operatorname{fst}(t_1))) \times \operatorname{Path}(x.B[px/a], \operatorname{snd}(t_0), \operatorname{snd}(t_1))$$

That is, a path in a product type is a product of paths.

*Proof.* In the forward direction, given $t : \operatorname{Path}(x.(a : A) \times B, t_0, t_1)$, we have the pair of paths $\langle \lambda^{\mathbb{I}}x. \operatorname{fst}(tx), \lambda^{\mathbb{I}}x. \operatorname{snd}(tx) \rangle$. In the reverse, given a pair of paths across the two types, $p : \operatorname{Path}(x.A, \operatorname{fst}(t_0), \operatorname{fst}(t_1))$ and $q : \operatorname{Path}(x.B[px/a], \operatorname{snd}(t_0), \operatorname{snd}(t_1))$, we have a path in the product type $\lambda^{\mathbb{I}}x. \langle px, qx \rangle$. It is straightforward to check that these two constructions are inverse up to exact equality. $\square$

The following characterization of paths in function types—a path between functions is a proof they are path-equal on all arguments—is similarly immediate.

**Lemma 3.2.5 (Function extensionality).** Let $A$ type and $x : \mathbb{I}, a : A \gg B$ type be given together with $f_0 : (a : A) \to B[0/x]$ and $f_1 : (a : A) \to B[1/x]$. Then we have an isomorphism of the following type.

$$\operatorname{Path}(x.(a : A) \to B, f_0, f_1) \simeq (a : A) \to \operatorname{Path}(x.B, f_0a, f_1a)$$

That is, a path in a function type is a family of paths when the domain is homogeneous.

*Proof.* Given $p$ in the former type, we have $\lambda a. \lambda^{\mathbb{I}}x. px a$ in the latter; given $h$ in the latter, we have $\lambda^{\mathbb{I}}x. \lambda a. hax$ in the former. These two constructions are clearly inverse up to exact equality. $\square$

The above is, however, limited to dependent paths $\operatorname{Path}(x.(a : A) \to B, F_0, F_1)$ where the domain type $A$ is independent of $x$. We can give a more general principle in the case