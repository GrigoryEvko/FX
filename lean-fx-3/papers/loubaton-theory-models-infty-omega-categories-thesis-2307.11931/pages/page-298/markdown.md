CHAPTER 5. THE (∞, 1)-CATEGORY OF MARKED (∞, ω)-CATEGORIES

such that for any object b of B♯, the outer square of the induced diagram

$$\begin{array}{ccc} A_{b/} & \xrightarrow{\pi'_b} & A & \xrightarrow{j} & C \\ v' \downarrow & & v \downarrow & & \downarrow^u \\ B_{/b}^\sharp & \xrightarrow{\pi_b} & B^\sharp & \xrightarrow{i} & D^\sharp \end{array}$$

verifies the weak Beck Chevaley condition. Then the right hand square verifies the Beck Chevaley condition.

Proof. Let E be an element of LCart(C). Using the hypothesis, the fact that πₐ is a right cartesian fibration, and so smooth, we have a sequence of equivalences:

$$\begin{array}{rcl} \perp \mathbf{R} \pi_b^* \mathbf{L} v_{!} \mathbf{R} j^* E & \sim & \perp \mathbf{L} v_{!}' \mathbf{R} \pi_b'^* \mathbf{R} j^* E & (5.2.4.21) \\ & \sim & \perp \mathbf{R} \pi_b^* \mathbf{R} i \mathbf{L} u_{!} E & (\text{hypothesis}) \end{array}$$

Using the equivalence (5.2.4.12), this implies that for any element b of B, we have an equivalence

$$\mathbf{R} b^* \mathbf{L} v_{!} \mathbf{R} j^* E \rightarrow \mathbf{R} b^* \mathbf{R} i \mathbf{L} u_{!} E$$

which concludes the proof as equivalences between left cartesian fibrations are detected fiberwise. □

Proposition 5.2.4.24. Let i : I → A♯ and j : C♯ → D♯ be two morphisms. The square

$$\begin{array}{ccc} C^\sharp \times I & \longrightarrow & D^\sharp \times I \\ \downarrow & & \downarrow \\ C^\sharp \times A^\sharp & \longrightarrow & D^\sharp \times A^\sharp \end{array}$$

verifies the Beck-Chevaley condition.

Proof. According to lemma 5.2.4.23, one has to show that for any pair (a, c) where a is an object of A♯ and c of C♯, the induced cartesian square

$$\begin{array}{ccc} C_{c/}^\sharp \times I_{a/} & \longrightarrow & D^\sharp \times I \\ \downarrow & & \downarrow \\ C_{c/}^\sharp \times A_{a/}^\sharp & \longrightarrow & D^\sharp \times A^\sharp \end{array}$$

verifies the weak Beck-Chevaley condition. Remark that this square factors as two cartesian squares:

$$\begin{array}{ccc} C_{c/}^\sharp \times I_{a/} & \longrightarrow & D_{j(c)/}^\sharp \times I_{a/} & \longrightarrow & D^\sharp \times I \\ \downarrow & & \downarrow & & \downarrow \\ C_{c/}^\sharp \times A_{a/}^\sharp & \longrightarrow & D_{j(c)/}^\sharp \times A_{a/}^\sharp & \longrightarrow & D^\sharp \times A^\sharp \end{array}$$

288