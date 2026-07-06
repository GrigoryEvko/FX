11:48

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

The only thing that remains is to add Löb induction. This is a modality-specific operation that cannot be expressed in the mode theory, so we must add it as an axiom:

$$\frac{\Gamma \operatorname{ctx} @ t \qquad \Gamma \vdash A \operatorname{type}_1 @ t}{\Gamma \vdash \operatorname{löb} : (\blacktriangleright A^{1 \leq \ell} \to A) \to A @ t}$$

$$\frac{\Gamma \operatorname{ctx} @ t \qquad \Gamma \vdash A \operatorname{type}_1 @ t \qquad \Gamma \vdash M : \blacktriangleright A^{1 \leq \ell} \to A @ t}{\Gamma \vdash \operatorname{löb}(M) = M(\operatorname{next}(\operatorname{löb}(M))) : (\blacktriangleright A^{1 \leq \ell} \to A) \to A @ t}$$

Notice that these rules are only added in mode $t$, as they only admit an interpretation in $\mathbf{PSh}(\omega)$ [BMSS12, §2]. Unfortunately, these ad-hoc additions mean that the canonicity theorem of Section 6 no longer applies.

9.4. Reasoning about Streams. We now put MTT to work: we will use it to reason about infinite streams defined by guarded recursion. We will demonstrate that the rules and axioms given in Section 9.3 suffice to carry out coinductive constructions. In particular, we will reproduce an example of $[\mathrm{BGC}^+ 16]$: we will show that $\operatorname{zipWith}(f)$ on a coinductive stream is commutative whenever $f$ itself is.

In order to simplify our working, we will swap the intensional equality type $\operatorname{Id}_A(M, N)$ with an extensional identity type $\operatorname{Eq}_A(M, N)$. This has the same introduction rule, but its elimination is replaced by the usual equality reflection rule

$$\frac{\Gamma \vdash P : \operatorname{Eq}_A(M_0, M_1) @ m}{\Gamma \vdash M_0 = M_1 : A @ m}$$

This is straightforwardly interpreted in the model, as both modes are mapped to presheaf toposes. The switch to extensional equality is not strictly necessary: we could carry out the following calculations with intensional identity, at the price of significantly more verbose terms. Moreover, the need for the function extensionality axiom would arise. However, adding Löb induction has already ensured that type-checking is undecidable, so nothing of value is lost by making the switch to extensional type theory for these examples.

We begin with a simple reasoning principle. Eliding $(-)^{1 \leq \ell}$ annotations:

Lemma 9.4. $(A : \mathsf{U})(x, y : \operatorname{El}(A)) \to \blacktriangleright \operatorname{Eq}_{\operatorname{El}(A)}(x, y) \to \operatorname{Eq}_{\blacktriangleright \operatorname{El}(A)}(\operatorname{next}(x), \operatorname{next}(y))$

Proof. Suppose $x, y : \operatorname{El}(A)$ and $p : \blacktriangleright \operatorname{Eq}_{\operatorname{El}(A)}(x, y)$; to show $\operatorname{next}(x) = \operatorname{next}(y) : \blacktriangleright \operatorname{El}(A)$. By congruence and the elimination rule for the modality, it suffices to prove $x = y : \operatorname{El}(A)$ in the locked context $A : \mathsf{U}, x : \operatorname{El}(A), y : \operatorname{El}(A), p : (\ell \mid \operatorname{Eq}_{\operatorname{El}(A)}(x, y)), \blacksquare_{\ell}$. But by the variable rule we have $p : \operatorname{Eq}_{\operatorname{El}(A)}(x, y)$ in this context, and hence $x = y : \operatorname{El}(A)$.

This can be used to prove internally that guarded fixed points are unique.

Theorem 9.5. $\operatorname{löb}(M)$ is the unique guarded fixed point of $M : \blacktriangleright \operatorname{El}(A) \to \operatorname{El}(A)$, i.e.

$$(A : \mathsf{U})(x : \operatorname{El}(A)) \to \operatorname{Eq}_{\operatorname{El}(A)}(M(\operatorname{next}(x)), x) \to \operatorname{Eq}_{\operatorname{El}(A)}(\operatorname{löb}(M), x)$$

Proof. Suppose $A : \mathsf{U}$; to show $(x : \operatorname{El}(A)) \to \operatorname{Eq}_{\operatorname{El}(A)}(M(\operatorname{next}(x)), x) \to \operatorname{Eq}_{\operatorname{El}(A)}(\operatorname{löb}(M), x)$ by Löb induction. Thus, assume that

$$f : \blacktriangleright ((x : \operatorname{El}(A)) \to \operatorname{Eq}_{\operatorname{El}(A)}(M(\operatorname{next}(x)), x) \to \operatorname{Eq}_{\operatorname{El}(A)}(\operatorname{löb}(M), x))$$