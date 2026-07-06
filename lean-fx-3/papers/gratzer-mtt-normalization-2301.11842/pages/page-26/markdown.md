27:26

NORMALIZATION FOR MULTIMODAL TYPE THEORY

Vol. 22:1

\(\mathbf{Prod}:(A:\mathsf{NfTy}_{m})(B:\mathsf{V}_{m}(A)\to \mathsf{NfTy}_{m})\to \mathsf{NfTy}_{m}\)

\(\mathbf{Sum}:(A:\mathsf{NfTy}_{m})(B:\mathsf{V}_{m}(A)\to \mathsf{NfTy}_{m})\to \mathsf{NfTy}_{m}\)

\(\mathbf{Id}:(A:\mathsf{NfTy}_{m})\to \mathsf{Nf}_{m}(A)\to \mathsf{Nf}_{m}(A)\to \mathsf{NfTy}_{m}\)

Bool : NfTy \( _{m} \)

\(\mathbf{Mod}_{\mu}:(\mu \mid \mathsf{NfTy}_n)\to \mathsf{NfTy}_m\)

\(\mathbf{lam}:(A:\bigcirc \mathrm{Ty}_m)(B:\bigcirc \mathrm{Tm}_m(A)\to \bigcirc \mathrm{Ty}_m)\)

\[
\rightarrow ((a: \mathrm{V} _ {m} (A)) \rightarrow \mathrm{Nf} _ {m} (B (a))) \rightarrow \mathrm{Nf} _ {m} (\operatorname{Prod} (A, B))
\]

\(\mathbf{app}:(\mu \mid A:\bigcirc \mathrm{Ty}_m)(B:\bigcirc \mathrm{Tm}_m(A)\to \bigcirc \mathrm{Ty}_m)\)

\[
\rightarrow \operatorname{Ne} _ {m} (\operatorname{Prod} (A, B)) \rightarrow (\mu \mid a: \operatorname{Nf} _ {m} (A)) \rightarrow \operatorname{Ne} _ {m} (B (a))
\]

up : Ne\( _{m} \)(Bool) → Nf\( _{m} \)(Bool)

tt, ff : Nf\( _{m} \)(Bool)

if :  \( (A : \mathsf{V}_{m}(\mathsf{Bool}) \to \mathsf{NfTy}_{m}) \)

\[
\rightarrow \operatorname{Nf} _ {m} (A (\text {true})) \rightarrow \operatorname{Nf} _ {m} (A (\text {false})) \rightarrow (b: \operatorname{Ne} _ {m} (\text {Bool})) \rightarrow \operatorname{Ne} _ {m} (A (b))
\]

\(\mathbf{up}:(A:\bigcirc \mathrm{Ty}_m)(a_0,a_1:\bigcirc \mathrm{Tm}_m(A))\)

\[
\rightarrow \operatorname{Ne} _ {m} (\operatorname{Id} (A, a _ {0}, a _ {1})) \rightarrow \operatorname{Nf} _ {m} (\operatorname{Id} (A, a _ {0}, a _ {1}))
\]

\(\mathbf{refl}:(A:\bigcirc_{z}\mathrm{Ty}_{m}(z))(a:\bigcirc_{z}\mathrm{Tm}_{m}(z,A(z)))\to \mathsf{Nf}_{m}(\mathsf{Id}(A,a,a))\)

\(\mathbf{J}:(A:\bigcirc \mathrm{Ty}_m)(B:(a_0,a_1:\mathsf{V}_m(A))(p:\mathsf{V}_m(\mathsf{Id}(A,a_0,a_1)))\to \mathsf{NfTy}_m)\)

\[
\rightarrow ((a: \mathrm{V} _ {m} (A)) \rightarrow \mathrm{Nf} _ {m} (B (a, a, \operatorname{refl} (a)))) (a _ {0}, a _ {1}: \bigcirc_ {z} \mathrm{Tm} _ {m} (A)) (p: \mathrm{Ne} _ {m} (\mathrm{Id} (A, a _ {0}, a _ {1})))
\]

\[
\rightarrow \operatorname{Ne} _ {m} (B (a _ {0}, a _ {1}, p))
\]

\(\mathbf{up}:(\mu \mid A:\mathsf{Ty}_n)\to \mathsf{Ne}_m(\mathsf{Mod}_\mu (A))\to \mathsf{Nf}_m(\mathsf{Mod}_\mu (A))\)

\(\mathbf{mod}_{\mu}:(\mu \mid A:\bigcirc \mathrm{Ty}_n)(\mu \mid \mathsf{Nf}_n(A))\to \mathsf{Nf}_m(\lambda z.\mathsf{Mod}_{\mu}(z,A(z)))\)

\(\mathbf{letmod}_{\mu ;\nu}:(\nu \circ \mu \mid A:\bigcirc \mathrm{Ty}_n)(B:(\nu \mid a:\mathsf{V}_m(\mathsf{Mod}_\mu (A)))\to \mathsf{NfTy}_o)\)

\[
\rightarrow ((\nu \circ \mu \mid a: \mathrm{V} _ {n} (A)) \rightarrow \mathrm{Nf} _ {o} (B (\mathfrak {m} _ {\mu} (a)))) \rightarrow (\nu \mid a: \mathrm{Ne} _ {m} (\mathrm{Mod} _ {\mu} (A))) \rightarrow \mathrm{Ne} _ {o} (B (a))
\]

Uni : NfTy \( _{m} \)

\(\mathbf{El}:\mathsf{Nf}_{m}(\mathsf{Uni})\to \mathsf{NfTy}_{m}\)

up : Ne\( _{m} \)(Uni) → Nf\( _{m} \)(Uni)

\(\widehat{\mathbf{Mod}}_{\mu}:(\mu \mid \mathrm{Nf}_n(\mathrm{Uni}))\to \mathrm{Nf}_m(\mathrm{Uni})\)

\(\mathbf{dec}_{\widehat{\mathbf{Mod}}_{\mu}}^{\triangleright}:(\mu \mid A:\mathsf{Nf}_{n}(\mathsf{Uni}))\to \mathsf{Nf}_{m}(\mathsf{Mod}_{\mu}(A))\to \mathsf{Nf}_{m}(\mathsf{El}(\widehat{\mathsf{Mod}}(A)))\)

\(\mathbf{dec}_{\widehat{\mathbf{Mod}}_{\mu}}^{\triangleleft}:(\mu \mid A:\mathsf{Nf}_{n}(\mathsf{Uni}))\to \mathsf{Ne}_{m}(\mathsf{El}(\widehat{\mathsf{Mod}}(A)))\to \mathsf{Ne}_{m}(\mathsf{Mod}_{\mu}(A))\)

Figure 5: Neutral and normal forms, internally