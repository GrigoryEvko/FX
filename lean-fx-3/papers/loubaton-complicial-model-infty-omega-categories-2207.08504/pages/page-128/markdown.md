CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

is also homotopy cocartesian, this implies that

$$C \coprod_{[a,1]} \tau_n^i([a,1]) \to \tau_n^i([a',1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a,1])$$

is an acyclic cofibration. Suppose now that there exists a family of morphisms $(x_k : [a_k, 1])_{k \le m} \to C$ such that $x_0 = x$, $x_m = y$ and for any $k$, $x_k$ and $x_{k+1}$ fulfill one of the three cases of definition 3.2.4.5. We then have two homotopy cocartesian squares:

$$\begin{array}{ccc} C \coprod_{[a',1]} \tau_n^i[a',1] & \longleftrightarrow & [a,1] \longrightarrow C \\ \downarrow & & \downarrow \\ C \coprod_{\coprod_{k \le m}[a_k,1]} \coprod_{k \le m} \tau_n^i[a_k,1] & \longleftrightarrow & \tau_n^i[a,1] \longrightarrow C \coprod_{\coprod_{k \le m}[a_k,1]} \coprod_{k \le m} \tau_n^i[a_k,1] \end{array}$$

As before, this implies that

$$C \coprod_{[a,1]} \tau_n^i([a,1]) \to C \coprod_{\coprod_{k \le m}[a_k,1]} \coprod_{k \le m} \tau_n^i[a_k,1]$$

and

$$\tau_n^i([a',1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a,1]) \to C \coprod_{\coprod_{k \le m}[a_k,1]} \coprod_{k \le m} \tau_n^i[a_k,1]$$

are acyclic cofibrations. By two out of three, this implies the result.

One can show similarly:

**Proposition 3.2.4.8.** Let $C$ be a stratified Segal $A$-precategory, and $x : [a,1] \to C$, $y : [a',1] \to C$ and $z : [a'',1] \to C$ three morphisms such that $(x,y) \ge_n z$. The morphism

$$\tau_n^i([a',1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a,1]) \to \tau_n^i([a',1]) \coprod_{[a',1]} C \coprod_{[a,1]} \tau_n^i([a,1]) \coprod_{[a'',1]} \tau_n^i([a'',1])$$

is an acyclic cofibration.

**Lemma 3.2.4.9.** Let $n$ be a non null integer and $a$ an element such that $\tau_n^i(a) = a$. The object $[2]^2 \otimes a$ is $n$-relying on $d^1 \bar{\otimes} a : e \star a \to [2]^2 \bar{\otimes} a$.

*Proof.* As the morphism $d^1 \bar{\otimes} a : e \star a \to [2]^2 \bar{\otimes} a$ is a weak equivalence, so are the horizontal morphisms of the following diagram:

$$\begin{array}{ccc} [k] \star e \star a & \xrightarrow{\sim} & [k] \star ([2]^2 \bar{\otimes} a) \\ \downarrow & & \downarrow \\ \tau_{n+k+1}^i([k] \star e \star a) & \xrightarrow{\sim} & \tau_{n+k+1}^i([k] \star ([2]^2 \bar{\otimes} a)) \end{array}$$

As the vertical morphisms are cofibrations, this implies that this square is homotopy cocartesian.

**Lemma 3.2.4.10.** Let $n$ be a non null integer and $a$ an element such that $\tau_n^i(a) = a$. The object $[2] \bar{\otimes} a$ is $n$-relying on $d^0 \otimes a : [1] \otimes a \to [2] \bar{\otimes} a$ and $d^2 \otimes a : e \star a \to [2] \otimes a$. Moreover, $[2] \bar{\otimes} a \coprod_{d^0 \otimes a} \tau_n^i([1] \otimes a)$ (resp. $[2] \bar{\otimes} a \coprod_{d^2 \bar{\otimes} a} \tau_n^i(e \star a)$) is $n$-relying on $d^2 \otimes a$ (resp. $d^0 \bar{\otimes} a$).

128