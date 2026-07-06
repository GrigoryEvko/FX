6.2. YONEDA LEMMA AND APPLICATIONS

Proposition 6.2.1.10. Let A be an locally U-small  \( (\infty,\omega) \) -category. Let a be an object of A. There is an equivalence

\[
\int_ {A} \hom_ {A} (a, \_) \to \mathbf {F} h _ {a} ^ {A}
\]

Taking the fibers on \(a\), the induced morphism \(\mathrm{hom}_A(a,a) \to \mathrm{hom}_A(a,a)\) preserves the identity. In particular, for any object \(c\) of \(C\), this induces an equivalence

\[
\int_ {C ^ {t}} y _ {c} \rightarrow \mathbf {F} h _ {c} ^ {C ^ {t}}
\]

Proof. By construction, \(\int_{A} \mathrm{hom}_{A}(a, \underline{\quad})\) is the Grothendieck construction of the left fibration:

\[
\begin{array}{l} \dots \quad \coprod_ {x _ {0}, x _ {1}, x _ {2}: A _ {0}} \hom_ {A} (a, x _ {0}, x _ {1}, x _ {2}) \stackrel {{\leftrightarrow}} {{\underset {\leftrightarrow} {\longrightarrow}}} \coprod_ {x _ {0}, x _ {1}: A _ {0}} \hom_ {A} (a, x _ {0}, x _ {1}) \stackrel {{\leftrightarrow}} {{\underset {\leftrightarrow} {\longrightarrow}}} \coprod_ {x _ {0}: A _ {0}} \hom_ {A} (a, x _ {0}) \\ \begin{array}{c c c c} \Big \downarrow & & \Big \downarrow & \\ \dots & \coprod_ {x _ {0}, x _ {1}, x _ {2}: A _ {0}} \hom_ {A} (x _ {0}, x _ {1}, x _ {2}) & \stackrel {{\longrightarrow}} {{\longleftrightarrow}} \coprod_ {x _ {0}, x _ {1}: A _ {0}} \hom_ {A} (x _ {0}, x _ {1}) & \stackrel {{\longleftrightarrow}} {{\longleftrightarrow}} \coprod_ {x _ {0}: A _ {0}} 1 \end{array} \\ \end{array}
\]

The results then follow from the corollary 6.1.2.17.

□

6.2.1.11. The identity \(\widehat{C} \to \widehat{C}\) induces by currying a canonical morphism

\[
\operatorname{ev}: C ^ {t} \times \widehat {C} \to \underline {{\omega}}
\]

called the evaluation functor. Given an object \(c\) of \(C\) and \(f\) of \(\widehat{C}\), we then have \(\mathrm{ev}(c, f) \sim f(c)\) and so

\[
(c, \{f \}) ^ {*} \int_ {C \times \widehat {C}} \mathrm{ev} \sim c ^ {*} \int_ {C ^ {t}} f
\]

Let \(E\) be an object of \((\infty, \omega)\)-\(\mathrm{cat}_{\mathrm{m} / \widehat{C}^{\sharp}}\) corresponding to a morphism \(g: X \to \widehat{C}^{\sharp}\). We denote \(\iota: X \to X^{\sharp}\) the canonical inclusion. A morphism

\[
E \rightarrow \int_ {\widehat {C}} \mathrm{ev} (c, \_)
\]

corresponds by adjunction to a morphism

\[
i d _ {X} \rightarrow g ^ {*} \int_ {\widehat {C}} \mathrm{ev} (c, \_) \tag {6.2.1.12}
\]

However, we have a canonical commutative square

\[
\begin{array}{c} X ^ {\sharp} \xrightarrow {g ^ {\sharp}} \widehat {C} \\ X ^ {\sharp} \times \{c \} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \mathrm{ev} (c, \_) \\ X ^ {\sharp} \times C ^ {t} \xrightarrow [ \widehat {g} ]{} \underline {{\omega}} \end{array}
\]

339