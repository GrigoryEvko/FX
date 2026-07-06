# 3. *Fibrations are the isofibrations.*

*Furthermore, this models structure is cofibrantly generated. The sets*

$$I := \{ \mathbf{0} \xrightarrow{u} \mathbf{1}, \{0\} \sqcup \{1\} \xrightarrow{v} \mathbf{2}, P \xrightarrow{w} \mathbf{2} \} \text{ and } J := \{ \mathbf{1} \to \mathcal{J} \}$$

*are the generating cofibrations and trivial cofibrations respectively.*

In this model structure all objects are cofibrant. We can immediately associate for each generator in $I$ a sort in the following way:

$$\begin{array}{ccc} \mathbf{0} \to \mathbf{1} & \longmapsto & \vdash \text{Ob Type} \\ \{0\} \sqcup \{1\} \to \mathbf{2} & \longmapsto & x, y : \text{Ob} \vdash \text{Hom}(x, y) \text{ Type} \\ P & \longmapsto & x, y : \text{Ob}, f, g : \text{Hom}(x, y) \vdash \text{Eq}(f, g) \text{ Type} \end{array}$$

Note that while the type $\text{Ob}$ has no dependencies, the type $\text{Hom}(x, y)$ depends on two elements of type $\text{Ob}$, which is encoded in the cofibration $\{0\} \sqcup \{1\} \to \mathbf{2}$. The same situation applies with the type $\text{Eq}$ which furthermore has dependencies on the types $\text{Ob}$ and $\text{Hom}$, now the cofibration $P \hookrightarrow \mathbf{2}$ expresses this.

*Remark 3.10.* The reason the previous association is well-defined is that the set of generating cofibrations $I$ of the model structure on $\text{Cat}$ from theorem 3.9 has a natural well-founded order—in the sense of theorem 3.2. Indeed, we can set $\mathbf{0} \to \mathbf{1}$ as the least element. Since the domain of the cofibration $\{0\} \sqcup \{1\} \to \mathbf{2}$ is a pushout of $\mathbf{0} \to \mathbf{1}$, we can declare $(\mathbf{0} \to \mathbf{1}) < (\{0\} \sqcup \{1\} \to \mathbf{2})$. Following the same reasoning, we see that the domain of the cofibration $P \to \mathbf{2}$ is the pushout of two copies of $\{0\} \sqcup \{1\} \to \mathbf{2}$. Therefore, we can also set $(\{0\} \sqcup \{1\} \to \mathbf{2}) < (P \to \mathbf{2})$. This completely determines the order $<$ on $I$, which is well-founded by construction. For all the subsequent examples, one can induce the corresponding well-founded orders analogously.

The resulting theory is what we introduced earlier, $\text{Cat}_=$, which for convenience we recall here. This is defined as:

1. Type of objects: $\vdash \text{Ob Type}$.
2. Type of morphisms: $x : \text{Ob}, y : \text{Ob} \vdash \text{Hom}(x, y) \text{ Type}$.
3. Equality type: $x, y : \text{Ob}, f, g : \text{Hom}(x, y) \vdash \text{Eq}(f, g) \text{ Type}$
4. Composition operation: $x, y, z : \text{Ob}, f : \text{Hom}(x, y), g : \text{Hom}(y, z) \vdash g \circ f : \text{Hom}(x, z)$.

34