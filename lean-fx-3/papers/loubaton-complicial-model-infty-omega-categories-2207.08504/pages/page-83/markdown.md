2.3. SUSPENSION AND GRAY OPERATIONS

Proof. We consider the diagram:

$$\begin{array}{c} [1] \longleftarrow [1] \coprod_{[0]} \Sigma X \longrightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma(X \otimes [1]) \coprod_{\Sigma X} [1] \vee \Sigma X \\ \downarrow{id} \qquad \sim \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow{id} \\ [1] \longleftarrow [1] \vee \Sigma X \longrightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma(X \otimes [1]) \coprod_{\Sigma X} [1] \vee \Sigma X \end{array}$$

All vertical morphisms are weak equivalences. We denote by $A$ the colimit of the first line. The theorem 2.3.1.1 implies that there is a zigzag of acyclic cofibrations between $A$ and $X \diamond [0]$. Colimits of the two lines are homotopy colimits, and the comparison morphism is then an acyclic cofibration. We then have a zigzag of acyclic cofibrations:

$$X \star [0] \leftarrow X \diamond [0] \rightsquigarrow A \rightarrow \Sigma X \vee [1] \coprod_{\Sigma X} \Sigma([0] \stackrel{co}{\star} X)$$

The second assertion is demonstrated similarly.

Corollary 2.3.2.2. Let $f : C \to D$ be a fibration between complicial sets, and $K \to L$ a cofibration. If $f$ has the right lifting property against

$$\Sigma([0] \stackrel{co}{\star} K \cup \emptyset \star L) \rightarrow \Sigma([0] \stackrel{co}{\star} L),$$

then $f$ has the right lifting property against

$$(\Sigma K) \star [0] \cup (\Sigma L) \star \emptyset \rightarrow \Sigma K \star [0].$$

If $f$ has the right lifting property against $\Sigma[1] \rightarrow \Sigma[1]_t$, then $f$ has the right lifting property against

$$[1]_t \star \emptyset \cup [1] \star [0] \rightarrow [1]_t \star [0]$$

Proof. Suppose that $f$ fulfills the condition. The class of cofibration having the right lifting property against $f$ is closed by pushouts and, according to 2.1.1.15, by zigzag of acyclic cofibration. The morphism

$$\alpha : \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K \coprod_{\emptyset \star K} \emptyset \star L) \rightarrow \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} L)$$

is then in this class. Remark that we have a cocartesian square

$$\begin{array}{c} \Sigma L \cup [1] \coprod_{\Sigma K \cup [1]} \Sigma K \vee [1] \longrightarrow \Sigma L \cup [1] \coprod_{\Sigma K \cup [1]} \Sigma K \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \Sigma L \vee [1] \longrightarrow \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K \coprod_{\emptyset \star K} \emptyset \star L) \end{array}$$

where the left vertical morphism, and so also the right vertical morphism, is an acyclic cofibration. This induces a zigzag of acyclic cofibration between $\alpha$ and $\beta$ where $\beta$ is

$$\Sigma L \cup [1] \coprod_{\Sigma K \cup [1]} \Sigma K \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} K) \rightarrow \Sigma L \vee [1] \coprod_{\Sigma L} \Sigma([0] \stackrel{co}{\star} L)$$

Eventually, the theorem 2.3.2.1 induces a zigzag of acyclic cofibration between $\beta$ and $(\Sigma K) \star [0] \cup (\Sigma L) \star \emptyset \rightarrow \Sigma K \star [0]$ which concludes the proof of the first assertion.

83