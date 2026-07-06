because it makes it easier to compute  \( ^{d} \)  of them:

\[
\Gamma \vdash_ {s m} S S T _ {\ell} ^ {d} \text { type } _ {\text { l   s   u   c } \ell} / A _ {3}: S S T _ {\ell}
\]

\[
\Gamma \vdash_ {s m} Z ^ {d}: ((\text {   EI   } (Z A _ {3}) \rightarrow \text { Type } _ {\ell})) _ {\{A _ {3}: S S T _ {\ell} \}, A _ {x}: S S T _ {\ell} ^ {d} A _ {3}}
\]

\[
\Gamma \vdash_ {s m} S ^ {d}: \left(\left(S S T _ {\ell} ^ {d d} A _ {3} A _ {x} (S A _ {3} a _ {3})\right)\right) _ {\{A _ {3}: S S T _ {\ell} \}, A _ {x}: S S T _ {\ell} ^ {d} A _ {3}, a _ {3}: E I (Z A _ {3}), a _ {x}: E I (Z ^ {d} A _ {x} a _ {3})}
\]

What this calculation suggests is that the family  \( SST^{d} \)  should behave as though defined by computing  \( ^{d} \)  on all of the destructors in the code block above:

codata  \( SST^{d} \)  ( \( A_{3} \)  : SST) : Type where
 \( Z^{d} \)  :  \( SST^{d} \)   \( A \rightarrow Z \)   \( A \rightarrow Type \) 
 \( S^{d} \)  : ( \( A_{x} \)  :  \( SST^{d} \)   \( A \) ) ( \( a_{3} \)  :  \( Z \)   \( A_{3} \) ) →  \( Z^{d} \)   \( A_{x} \)   \( a_{3} \)  →  \( SST^{dd} \)   \( A_{3} \)   \( A_{x} \)  ( \( S \)   \( A_{3} \)   \( a_{3} \) )

Unfortunately, as we will see this is not actually possible in our theory, but it is a useful intuition. In general, the types obtained by iterating  \( ^{d} \)  n-times on Z and S will begin by taking a n-fold dependent SST in a generic augmented simplicial context of SSTs of lower dependency. This context can be generally inferred from the type of n-fold dependent SST, and we have thus chosen to make those arguments implicit, which aligns with the syntactic presentation in the introduction. In particular, the formula for  \( A_{2} \)  is given by:

\[
Z ^ {d d} \left(S ^ {d} (S A x _ {m}) x _ {m} \beta_ {m}\right) x _ {m} \beta_ {m} \beta_ {m}
\]

as opposed to:

\[
Z ^ {d d} A (S A x _ {m}) (S A x _ {m}) \left(S ^ {d} A (S A x _ {m}) x _ {m} \beta_ {m}\right) x _ {m} \beta_ {m} \beta_ {m}.
\]

#### 3.1.2 The coinduction principle

Suppose that we want to construct a function mapping into SST from a telescope of arbitrary length. We first think purely in terms of code, written in the style of Agda-esque copattern matching, with the goal of writing down something that can conceivably be justified:

f : X → SST
Z (f t) = (?z₀ : Type)
S (f t) a = fᵈ t (?s₀ : Xᵈ t)
g : (t : X) → Y t → SST
Z (g t s) = (?z₁ : Type)
S (g t s) a = gᵈ t (?s₁ : Xᵈ t) s (?s₂ : Yᵈ t ?s₁ s)

Here, suppose that \(\Gamma\), \(\widehat{\mathbf{Q}}_{\Delta \square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell'}\). If we think of \(\Upsilon\) as a state space and \([\sigma : \Upsilon]\) as a state. Then the above definition suggests that we are able to define \(f: (\upsilon : \Upsilon) \to \mathrm{SST}_{\ell}\) provided that we are able to provide two ingredients. First, we need a way of extracting \([\bar{Z} \sigma : \mathrm{Type}_{\ell}]\), a type of 0-simplices, from a state \(\sigma\). Second, we need a way of extracting \([\bar{S} \sigma a : \Upsilon^{d} \sigma]\), a dependent section of \(\Upsilon\) over \(\sigma\), from a state \(\sigma\) and a 0-simplex \([a : \bar{Z} \sigma]\). This suggests that a reasonable coinduction principle for \(\mathrm{SST}_{\ell}\) is the following:

\[
\frac {\Gamma , \widehat {\mathbf {Q}} _ {\Delta \square} \vdash_ {\mathrm{sm}} \Upsilon \operatorname{ctx} _ {\ell^ {\prime}}}{\Gamma , \widehat {\mathbf {Q}} _ {\Delta \square} \vdash_ {\mathrm{sm}} \bar {Z} : ((\text {Type} _ {\ell})) _ {\delta : \Upsilon} \quad \Gamma , \widehat {\mathbf {Q}} _ {\Delta \square} \vdash_ {\mathrm{sm}} \bar {S} : ((\Upsilon^ {d} \delta)) _ {\delta : \Upsilon , a : \operatorname{EI} (\bar {Z} \delta)}}   \frac {}{\Gamma \vdash_ {\mathrm{sm}} R _ {T} \bar {Z} \bar {S} : ((\text {SST} _ {\ell})) _ {\delta : \Upsilon}}
\]

30