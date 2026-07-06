Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:5

In lieu of an exhaustive list of rules, which we will present in Section 4, we illustrate this point by only showing the important ones in Figure 1. In brief, each mode comprises an ordinary intensional type theory with dependent sums, dependent products, intensional identity types, booleans, and one universe. Both sums and products satisfy an $\eta$-rule.

**Universes à la Coquand.** There are several ways to introduce universes in type theory [Hof97, §2.1.6] [Pal98, Luo12]. We use the approach of [Coq13], which is close to Tarski-style universes. However, instead of inductively defining *codes* that represent particular types, Coquand-style universes come with an *explicit isomorphism* between types and terms of the universe U. However, we must remember to exercise caution: if this isomorphism were to cover all types then *Girard's paradox* [Coq86] would apply, so we must restrict it to *small types*. This, in turn, forces us to stratify our types into small and large.

The judgment $\Gamma \vdash A \text{ type}_0 @ m$ states that $A$ is a small type, and $\Gamma \vdash A \text{ type}_1 @ m$ that it is large. The universe itself must be a large type, but otherwise both levels are closed under all other connectives. Finally, we introduce an operator that *lifts* a small type to a large one:

$$\frac{\ell \leq \ell' \quad \Gamma \vdash A \text{ type}_\ell @ m}{\Gamma \vdash \Uparrow A \text{ type}_{\ell'} @ m}$$

The lifting operation commutes definitionally with all the connectives, e.g. $\Uparrow(A \to B) = \Uparrow A \to \Uparrow B$. We will use large types for the most part: only they will be allowed in contexts, and the judgment $\Gamma \vdash M : A @ m$ will presuppose that $A$ is large. As we will not have terms at small types, we will not need the term lifting operations used by [Coq13] and [Ste19].

Following this stratification, we may introduce operations that exhibit the isomorphism:

$$\frac{\Gamma \vdash M : \mathsf{U} @ m}{\Gamma \vdash \mathsf{El}(M) \text{ type}_0 @ m}$$

$$\frac{\Gamma \vdash A \text{ type}_0 @ m}{\Gamma \vdash \mathsf{Code}(A) : \mathsf{U} @ m}$$

along with the equations $\mathsf{Code}(\mathsf{El}(M)) = M$ and $\mathsf{El}(\mathsf{Code}(A)) = A$.

The advantages of universes à la Coquand are now evident: rather than having to introduce Tarski-style codes, we now find that they are *definable*. For example, assuming $M : \mathsf{U}$ and $x : \mathsf{El}(M) \vdash N : \mathsf{U}$, we let

$$(x : M) \xrightarrow{\sim} N \triangleq \mathsf{Code}((x : \mathsf{El}(M)) \to \mathsf{El}(N)) : \mathsf{U}$$

We can then calculate that

$$\mathsf{El}((x : M) \xrightarrow{\sim} N) = \mathsf{El}(\mathsf{Code}((x : \mathsf{El}(M)) \to \mathsf{El}(N))) = (x : \mathsf{El}(M)) \to \mathsf{El}(N)$$

We will often suppress $\Uparrow-$ as well as the explicit isomorphism.

**2.2. Introducing a Modality.** Having sketched the basic type theory inhabiting each mode, we now turn to the interaction between them. This is the domain of the modalities.

Suppose $\mathcal{M}$ contains a modality $\mu : n \to m$. We would like to think of $\mu$ as a 'map' from mode $n$ to mode $m$. Then, for each $\vdash A \text{ type } @ n$ we would like a type $\vdash \langle \mu \mid A \rangle \text{ type } @ m$. On the level of terms we would similarly like for each $\vdash M : A @ n$ an induced term $\vdash \mathsf{mod}_\mu(M) : \langle \mu \mid A \rangle @ m$.

These constructs would be entirely satisfactory, were it not for the presence of *open terms*. To illustrate the problem, suppose we have a type $\Gamma \vdash A \text{ type } @ n$. We would hope that the corresponding modal type lives in the same context, i.e. that $\Gamma \vdash \langle \mu \mid A \rangle \text{ type } @ m$. However, this is not possible, as $\Gamma$ is only a context at mode $n$, and cannot be carried over