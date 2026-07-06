### 3.3 DISPLAYED COINDUCTIVE TYPES

Generalizing the discussion of SST, we now formulate a fairly general notion of 'indexed displayed coinductive type'. It depends on a telescope \(\Phi\) of 'non-uniform parameters', and every element of it has a 'head' belonging to some specified type family \(A\) and a 'tail', depending on a telescope of parameters \(\mathcal{B}\), and belonging to the displayed version of the coinductive type itself. The parameters of this displayed version of the very type being defined are \(\Phi^{\mathrm{D}}\), which we can assemble provided that the data of the old parameters \(\varphi : \Phi\), the head \(x: A \varphi\), and the new dependencies \(b: \mathcal{B} \varphi a\), are sufficient to extract a section \(\sigma \varphi x b: \Phi^{\mathrm{d}} \varphi\). The idea is analogous to an 'indexed M-type', but with the output of the tail being displayed, and with \(\mathcal{B}\) being a telescope rather than a simple type. The pseudo-Agda corresponding to this would be:

module = (Φ : △□ Tel) (A : △□ Φ → Type) (B : △□ (φ : Φ) (a : A φ) → Tel)
(σ : △□ (φ : Φ) (a : A φ) (b : B φ a) → Φ\( ^{d} \) φ) where
codata dCoind (φ : Φ) : Type where
head : dCoind φ → A φ
tail : (x : dCoind φ) (b : B φ (head x)) → dCoind\( ^{d} \) ⟨φ , σ φ (head x) b⟩ x

We can thus write down the formation and introduction rules for dCoind as follows:

\(\begin{array}{c}\Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\Phi \operatorname {tel}_{\ell_0}\qquad \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\Lambda \operatorname {type}_{\ell_1} / \varphi :\Phi \\ \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\mathcal{B}\operatorname {tel}_{\ell_2} / \varphi :\Phi ,a:A\varphi \qquad \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\sigma :\left(\left(\Phi^{\mathrm{d}}\varphi\right)\right)_{\varphi :\Phi ,a:A\varphi ,b:\mathcal{B}\varphi x}\\ \hline \Gamma \vdash_{\mathrm{sm}}\mathrm{dCoind}_{[\Phi ,A,\mathcal{B},\sigma ]}\operatorname {type}_{\ell_1\sqcup \ell_2} / \varphi :\Phi [\mathbf{a}_{\mathbf{a}}\triangle \square \leqslant 1_{\mathrm{sm}}]\\ \Gamma \vdash_{\mathrm{sm}}\operatorname {head}_{[\Phi ,A,\mathcal{B},\sigma ]}:(A[\mathbf{a}_{\mathbf{a}}\triangle \square \leqslant 1_{\mathrm{sm}}]\varphi))_{\varphi ,x:\mathrm{dCoind}_{[\Phi ,A,\mathcal{B},\sigma ]}}\varphi \\ \Gamma \vdash_{\mathrm{sm}}\operatorname {tail}_{[\Phi ,A,\mathcal{B},\sigma ]}:(dCoind_{[\Phi ,A,\mathcal{B},\sigma ]}^{\mathrm{d}}\langle \varphi ,\sigma \varphi (\operatorname {head}x)b\rangle x))_{\varphi ,x,b:\mathcal{B}[\mathbf{a}_{\mathbf{a}}\triangle \square \leqslant 1_{\mathrm{sm}}]\varphi (\operatorname {head}\varphi x)} \end{array}\)

Note that the universe level of dCoind is governed by those of A and B, but does not depend on the level of the telescope of non-uniform parameters  \( \Phi \) .

Following the example of SST, we will begin by attempting to write down a reasonable template for a coinduction principle. In the same module context, we can attempt to map into a dCoind type from a length two context as follows:

f : (t : X) (s : Y t) → dCoind (φ t s)
head (f t s) = (?h₁ : A (φ t s))
tail (f t s) b = fᵈ t (?t₁ : Xᵈ t) s (?t₂ : Yᵈ t ?t₁ s)

The types that we have are then:

\[
\text { tail } (f t s) b: d \text { Coind } ^ {d} \langle \phi t s, \sigma (\phi t s)? _ {h _ {1}} b \rangle (f t s)
\]

\[
f ^ {d} t? _ {t _ {1}} s? _ {t _ {2}}: d \text { Coind } ^ {d} \langle \phi t s, \phi^ {d} t? _ {t _ {1}} s? _ {t _ {2}} \rangle (f t s)
\]

Thus there is a non-trivial condition that needs to be imposed for this definition template to be well typed. Fortunately, unlike in the case of  \( SST^{d} \) , we generally have terms lining up in the sense that the terminal (f t s) terms align, which avoids the vicious cycle from before. We get the following rule:

\(\begin{array}{c}\Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\Upsilon \operatorname {tel}_{\ell^{\prime}}\qquad \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\phi :\left((\Phi)\right)_{v:\Upsilon}\\ \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\overline{h}:(A(\phi v))_{v:\Upsilon}\qquad \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}\vdash_{\mathrm{sm}}\overline{\tau}:((\Upsilon^{d}v))_{v:\Upsilon ,b:\mathcal{B}(\phi v)(\overline{h} v)}\\ \Gamma ,\widehat{\mathbf{a}}_{\triangle \square}|v:\Upsilon ,b:\mathcal{B}(\phi v)(\overline{h} v)\vdash \phi^{d}\langle v,\overline{\tau} v b\rangle \equiv \sigma (\phi v)(\overline{h} v)b\\ \hline \Gamma \vdash_{\mathrm{sm}}\operatorname {corec}_{[\Phi ,A,\mathcal{B},\sigma ]}[\Upsilon ,\phi ,\overline{h},\overline{\tau} ]:(dCoind_{[\Phi ,A,\mathcal{B},\sigma ]}(\phi v))_{v:\Upsilon} \end{array}\)

36