6.2. YONEDA LEMMA AND APPLICATIONS

Proof. As the proof of the two assertions are similar, we will only show the second one. To demonstrate this, it is enough to show that the induced natural transformation

$$\hom_C(a, v(b)) \xrightarrow{(\mu_{v(b)})!} \hom_C(a, vuv(b)) \xrightarrow{(v(\epsilon_{(b)}))!} \hom_C(a, v(b)) \xrightarrow{\phi^{-1}} \hom_D(u(a), b) \tag{6.2.2.14}$$

is equivalent to $\phi^{-1}$. By definition, the first morphism is equivalent to the composition

$$\hom_C(a, v(b)) \to \hom_D(u(a), uv(b)) \xrightarrow{\phi} \hom_C(a, vuv(b))$$

and as $\phi^{-1}$ is a natural transformation, we have a commutative square

$$\begin{array}{ccc} \hom_C(a, vuv(b)) & \xrightarrow{(v(\epsilon_b))!} & \hom_C(a, v(b)) \\ \phi^{-1} \downarrow & & \downarrow \phi^{-1} \\ \hom_C(u(a), uv(b)) & \xrightarrow{(\epsilon_b)!} & \hom_D(u(a), b) \end{array}$$

The composite of the sequence (6.2.2.14) is then equivalent to

$$\hom_C(a, v(b)) \to \hom_D(u(a), uv(b)) \xrightarrow{(\epsilon_b)!} \hom_D(u(a), b)$$

which is itself equivalent to $\phi^{-1}$ according to lemma 6.2.2.12.

Proof of theorem 6.2.2.9. The implication (1) $\Rightarrow$ (2) is given by proposition 6.2.2.5 and the contraposed by the lemma 6.2.2.13.

### 6.2.3 Lax colimits

6.2.3.1. According to corollary 6.2.2.7, a morphism $f : A \to B$ between U-small $(\infty, \omega)$-categories induces an adjoint pair:

$$f_! : \widehat{A} \xrightarrow{\perp} \widehat{B} : f^* \tag{6.2.3.2}$$

Proposition 6.2.3.3. Let $f : A \to B$ be a morphism between U-small $(\infty, \omega)$-categories. There is an equivalence

$$f_!(y_a) \sim y_{f(a)}$$

natural in $a : A$.

Proof. Consider the sequence of equivalences

$$\begin{array}{lcl} \hom_{\widehat{B}}(f_!(y_a), g) & \sim & \hom_{\widehat{A}}(y_a, f^*(g)) \quad (6.2.3.2) \\ & \sim & \operatorname{ev}(a, f^*(g)) \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(Yoneda lemma)} \\ & \sim & \operatorname{ev}(f(a), g) \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(naturality of ev)} \\ & \sim & \hom_{\widehat{B}}(y_{f(a)}, g) \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array}$$

Eventually, the Yoneda lemma applied to $(\widehat{B})^t$ concludes the proof.

349