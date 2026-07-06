1.2. GRAY OPERATIONS

and

$$w _ { i } ^ { - } = v _ { i } ^ { - } - \partial ( w _ { i + 1 } ^ { - } ) = v _ { i } ^ { - } - \partial ^ { + } ( w _ { i + 1 } ^ { - } ) + \partial ^ { - } ( w _ { i + 1 } ^ { - } ) \geq 0$$

The two assertions (1.2.2.12) and (1.2.2.13) are then fulfilled, which concludes the proof.

Lemma 1.2.2.14. Let $C$ be a $(0, 2)$-category with a atomic and loop free basis. Let $x$ be a element of the base of $C$, and $y$ an element of the base of $D$. Let $f : C \to D$ be a morphism such that $\lambda f x = y$. Let $u$ be an 2-cell of $C$. We denote by $u =: u_0 *_0 u_1 *_0 u_2$ and $f(u) =: v_0 *_1 v_1 *_1 v_2$ the decomposition given by the lemma 1.2.2.11. Then

$$f ( u _ { 0 } ) = v _ { 0 } \quad f ( u _ { 1 } ) = v _ { 1 } \quad f ( u _ { 2 } ) = v _ { 2 }$$

Proof. This is a direct consequence of lemma 1.2.2.14.

Lemma 1.2.2.15. Let $C$ be a $(0, 2)$-category with a atomic and loop free basis. Let $x$ be a element of the base of $C$, and $y$ an element of the base of $D$. Let $f : C \to D$ be a morphism such that $y$ belongs to $\lambda f x$. Let $u$ be an 2-cell of $C$. We denote by $u =: u_0 *_1 u_1 *_1 u_2$ and $f(u) =: v_0 *_1 v_1 *_1 v_2$ the decompositions given by lemma 1.2.2.11. For any $i \leq 2$, we denote by $f(u_i) =: u_{i0} *_1 u_{i1} *_1 u_{i2}$ the decomposition given by lemma op cit. Then

$$v _ { 0 } = u _ { 0 0 } \quad v _ { 1 } = u _ { 0 1 } * _ { 1 } u _ { 0 2 } * _ { 1 } u _ { 1 0 } * _ { 1 } u _ { 1 1 } * _ { 1 } u _ { 1 2 } * _ { 1 } u _ { 2 0 } * _ { 1 } u _ { 2 1 } \quad v _ { 2 } = u _ { 2 2 }$$

Proof. This is a direct consequence of lemma 1.2.2.14.

Notation 1.2.2.16. Let $a$ be a globular sum of dimension lower or equal to 2. We denote by $\nabla$ the unique algebraic morphism $\mathbf{D}_2 \to a$. The 2-cell $\nabla$ is called the composite cell of $a$.

Remark 1.2.2.17. If $i : a \to a'$ is an algebraic morphism, and $f : a' \to C$ any morphism, the composite cell of $f : a' \to C$ is the same as the composite cell of $f i : a \to C$.

Definition 1.2.2.18. Let $b$ be an element of the base of $D$. A 2-cell $v$ of $D$ is 0-comparable with $b$ if $b \in B_2^v$ and if for any $b' \in B_2^v$, the assertion $\neg(b <_1^v b') \land \neg(b' <_1^v b)$ holds.

Lemma 1.2.2.19. Let $a$ be a globular sum of dimension lower or equal to 2. Let $x$ be a 2-cell of $D$. Let $f : a \to D$ be a morphism such that $f(\nabla)$ is 0-comparable with $x$. Then there exists a commutative triangle

$$\begin{array}{c} a ^ { \prime } \vee [ [ 1 ], 1 ] \vee a ^ { \prime \prime } \\ \xrightarrow [ f ] { i } \xrightarrow [ f ^ { \prime } \vee x \vee f ^ { \prime \prime } ] { } \\ D \end{array}$$

Moreover, this factorization is functorial in $C$.

Proof. Let $d$ be the (necessarily unique) element of the basis of $a$ such that $x \in [f(d)]_2$. Let $k \leq 1$ and $j : [[k], 1] \to \mathrm{Sp}_a$ be an element of the basis, i.e., a globular morphism.

If $j = d$, we consider the diagram

$$\begin{array}{c} [ [ 1 ], 1 ] \vee [ [ 1 ], 1 ] \vee [ [ 1 ], 1 ] \\ \xrightarrow [ f j ] { } \xrightarrow [ f ^ { \prime } \vee x \vee f ^ { \prime \prime } ] { } \\ D \end{array}$$

35