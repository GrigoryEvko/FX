6.2. YONEDA LEMMA AND APPLICATIONS

Corollary 6.2.4.3. Let $i : A \to B$ be a morphism between U-small $(\infty, \omega)$-categories. The left Kan extension of the Yoneda embedding $y : A \to \widehat{A}$ along $i$ is $N_i : B \to \widehat{A}$.

Proof. According to proposition 6.2.4.2, the desired left Kan extension is given by

$$(B^t \times i)_! \operatorname{hom}_B$$

which is $N_i$ according to lemma 6.2.1.17.

Proposition 6.2.4.4. Let $i : A \to B$ a functor between U-small $(\infty, \omega)$-categories. The left Kan extension of $y^B \circ i$ along $y^A$ is given by $i_!$.

Proof. Let $i : A \to B$ be any functor. Remark first that the Yoneda lemma and the corollary 6.2.4.3 imply that the left Kan extension of $y : A \to \widehat{A}$ along $y : A \to \widehat{A}$ is the identity of $\widehat{A}$. We then have a sequence of equivalences

$$\begin{array}{l} \operatorname{hom}_{\underline{\operatorname{Hom}}(\widehat{A}, \widehat{A})}(i_!, f) \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(\widehat{A}, \widehat{A})}(id, i^* \circ f) \quad (6.2.2.7) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{A})}(y_A, i^* \circ f \circ y^A) \quad (\text{Yoneda lemma}) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{B})}(i_! \circ y^A, f \circ y^A) \quad (6.2.2.7) \\ \quad \sim \operatorname{hom}_{\underline{\operatorname{Hom}}(A, \widehat{B})}(y_B \circ i, f \circ y^A) \quad (6.2.3.3) \end{array}$$

natural in $f : \underline{\operatorname{Hom}}(\widehat{A}, \widehat{B})$.

Corollary 6.2.4.5. For any morphism $A \to B$ between U-small $(\infty, \omega)$-categories with $B$ lax U-cocomplete, there exists a unique colimit preserving functor $\widehat{A} \to B$ extending $i$.

Proof. Let $|\_|_i : \widehat{A} \to B$ be the functor defined in corollary 6.2.3.27. As this functor is an extension of $A$, it fulfills the desired condition, that shows the existence. The $(\infty, \omega)$-category of functors verifying the desired property is given by the pullback

$$\begin{array}{ccc} \underline{\operatorname{Hom}}_!(\widehat{A}, B)_i & \longrightarrow & \underline{\operatorname{Hom}}_!(\widehat{A}, B) \\ \downarrow & & \downarrow \\ \{i\} & \longrightarrow & \underline{\operatorname{Hom}}(A, B) \end{array}$$

where $\underline{\operatorname{Hom}}_!(\widehat{A}, B)$ is the full sub $(\infty, \omega)$-category of $\underline{\operatorname{Hom}}(\widehat{A}, B)$ whose objects are colimit preserving functors. As $|\_|_i$ is the left Kan extension of $i$ along the Yoneda embedding, there is a transformation

$$|_|_i \to h$$

natural in $h : \underline{\operatorname{Hom}}(\widehat{A}, B))_i$. To conclude, one has to show that for any object $h$ of $\underline{\operatorname{Hom}}(\widehat{A}, B))_i$, $|\_|_i \to h$ is an equivalence, and so that for any object $f$ of $\widehat{A}$, $|f|_i \to h(f)$ is an equivalence. As $f$ is a lax colimit of representables as shown in theorem 6.2.3.24 and as both $|\_|_i$ and $h$ preserve lax colimits, this is immediate.

361