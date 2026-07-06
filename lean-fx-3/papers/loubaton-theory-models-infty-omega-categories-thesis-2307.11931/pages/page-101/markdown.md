2.3. SUSPENSION AND GRAY OPERATIONS

and $\Sigma X \star [0]$.

There is a zigzag of acyclic cofibrations, natural in $X$, between the colimit of the diagram

$$\Sigma(X \star [0]) \leftarrow \Sigma X \rightarrow [1] \vee \Sigma X$$

and $[0] \stackrel{co}{\star} \Sigma X$.

Proof. We consider the diagram:

$$\begin{array}{ccc} [1] & \longleftarrow & [1] \coprod_{[0]} \Sigma X \longrightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma(X \otimes [1]) \coprod_{\Sigma X} [1] \vee \Sigma X \\ \downarrow{id} & & \sim \downarrow & \downarrow{id} \\ [1] & \longleftarrow & [1] \vee \Sigma X \longrightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma(X \otimes [1]) \coprod_{\Sigma X} [1] \vee \Sigma X \end{array}$$

All vertical morphisms are weak equivalences. We denote by $A$ the colimit of the first line. The theorem 2.3.1.1 implies that there is a zigzag of acyclic cofibrations between $A$ and $X \diamond [0]$. Colimits of the two lines are homotopy colimits, and the comparison morphism is then an acyclic cofibration. We then have a zigzag of acyclic cofibrations:

$$X \star [0] \leftarrow X \diamond [0] \rightsquigarrow A \rightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma([0] \stackrel{co}{\star} X)$$

The second assertion is demonstrated similarly. $\square$

**Corollary 2.3.2.2.** Let $f : C \rightarrow D$ be a fibration between complicial sets, and $K \rightarrow L$ a cofibration. If $f$ has the right lifting property against

$$\Sigma([0] \stackrel{co}{\star} K \cup \emptyset \star L) \rightarrow \Sigma([0] \stackrel{co}{\star} L),$$

then $f$ has the right lifting property against

$$(\Sigma K) \star [0] \cup (\Sigma L) \star \emptyset \rightarrow \Sigma K \star [0].$$

If $f$ has the right lifting property against $\Sigma[1] \rightarrow \Sigma[1]_t$, then $f$ has the right lifting property against

$$[1]_t \star \emptyset \cup [1] \star [0] \rightarrow [1]_t \star [0]$$

Proof. Suppose that $f$ fulfills the condition. The class of cofibration having the right lifting property against $f$ is closed by pushouts and, according to 2.1.1.15, by zigzag of acyclic cofibration. The morphism

$$\alpha : \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K \coprod_{\emptyset \star K} \emptyset \star L) \rightarrow \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} L)$$

91