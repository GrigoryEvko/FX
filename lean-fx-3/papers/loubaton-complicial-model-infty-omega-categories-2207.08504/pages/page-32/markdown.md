CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Proof. According to lemma 1.2.2.5, we have a well defined 0-composite

$$b * _ { 0 } \ldots * _ { 0 } b ^ { \prime }$$

and so a well defined 0-composite

$$f ( b ) * _ { 0 } \ldots * _ { 0 } f ( b ^ { \prime } )$$

Applying the decomposition given in theorem 1.2.2.7 to $f(b)$ and $f(b')$, we get a well-defined composite

$$w * _ { 0 } \ldots * _ { 0 } w ^ { \prime } .$$

where $w$ (resp. $w'$) is a 0-composite of $c$ (resp. $c'$) with 1-generators. This then implies $c < _ { 0 } ^ { f ( v ) } c'$.

We now deal with the second case. Let $c \in B _ { 2 } ^ { f ( b ) }$ and $c' \in B _ { 2 } ^ { f ( b ' ) }$. According to theorem 1.2.2.7 there exists a decomposition of $v$ of shape

$$v : = v _ { 0 } * v _ { 1 } * _ { 1 } \ldots * _ { 1 } v _ { n }$$

where for all $i \leq n$, $v_0$ is a 0-composite of a unique 2-generator with 1-generators. Moreover, the unique $i$ (resp. the unique $j$) such that $b$ belongs to $v_i$ (resp. such that $b'$ belongs to $v_j$) verifies $i < j$.

Applying the morphism $f$ and decomposing each $f(v_i)$ the same way, we get a decomposition

$$f ( v ) : = u _ { 0 } * u _ { 1 } * _ { 1 } \ldots * _ { 1 } u _ { m }$$

where for all $i \leq m$, $u_0$ is a 0-composite of a 2-generator with 1-generators, and such that the unique $i$ (resp. the unique $j$) such that $c$ belongs to $u_i$ (resp. such that $c'$ belongs to $w_j$) verifies $i < j$. The second assertion of theorem 1.2.2.7 then implies that $\neg(c' < _ { 1 } ^ { f ( v ) } c)$. □

Lemma 1.2.2.9. Let $v$ be a 2-cell, and $b, b'$ two different elements of the 2-support of $v$. Then $\neg(b < _ { 1 } ^ { v } b') \wedge \neg(b' < _ { 1 } ^ { v } b)$ implies that $(b < _ { 0 } ^ { v } b') \vee (b' < _ { 0 } ^ { v } b)$ holds.

Proof. We suppose that $\neg(b < _ { 1 } ^ { v } x) \wedge \neg(x < _ { 1 } ^ { v } b)$. We can then find an ordering with respect to $< _ { i } ^ { v }$ of $B _ { 2 } ^ { v }$ such that $b$ and $b'$ are one after the other. According to theorem 1.2.2.7, we have a decomposition of $v$ of shape $\ldots * _ { 1 } v _ { i } * _ { 1 } v _ { i + 1 } * _ { 1 } \ldots$ such that $v_i$ can be written as a 0-composite of $b$ and 1-generators and $v_{i+1}$ can be written in a 0-composite of $b'$ and 1-generators. We then have

$$v _ { i } : = \ldots * _ { 0 } b * _ { 0 } \ldots \quad v _ { i + 1 } : = \ldots * _ { 0 } b ^ { \prime } * _ { 0 } \ldots$$

and then an equality between the following 1-cells

$$\ldots * _ { 0 } \pi _ { 1 } ^ { - } b * _ { 0 } \ldots = \pi _ { 1 } ^ { - } v _ { i } = \pi _ { 1 } ^ { + } v _ { i + 1 } = \ldots * _ { 0 } \pi _ { 1 } ^ { + } b ^ { \prime } * _ { 0 } \ldots$$

As $\pi _ { 1 } ^ { - } b \wedge \pi _ { 1 } ^ { + } b ^ { \prime } = 0$, this implies that $\pi _ { 1 } ^ { - } v _ { i } = \pi _ { 1 } ^ { + } v _ { i + 1 }$ can be written as

$$\ldots * _ { 0 } \pi _ { 1 } ^ { - } b * _ { 0 } \ldots * _ { 0 } \pi _ { 1 } ^ { + } b ^ { \prime } * _ { 0 } \ldots \quad \mathrm { o r ~ a s } \quad \ldots * _ { 0 } \pi _ { 1 } ^ { + } b ^ { \prime } * _ { 0 } \ldots * _ { 0 } \pi _ { 1 } ^ { - } b * _ { 0 } \ldots$$

The cell $v_i * _ { 1 } v_{i+1}$ can then be written as

$$\ldots * _ { 0 } b * _ { 0 } \ldots * _ { 0 } b ^ { \prime } * _ { 0 } \ldots \quad \mathrm { o r ~ a s } \quad \ldots * _ { 0 } b ^ { \prime } * _ { 0 } \ldots * _ { 0 } b * _ { 0 } \ldots$$

This implies that $(b < _ { 0 } x) \vee (x < _ { 0 } b)$ holds.

Lemma 1.2.2.10. Let $v$ be a 2-cell, and $b, b'$ two elements of the 2-support of $v$. Then $b < _ { 0 } ^ { v } b'$ implies that for all $\alpha \in \{ -, + \}$, for all $c$ in $\langle b \rangle _ { 1 } ^ { \alpha }$, $c < _ { 0 } ^ { v } b'$ holds.

32