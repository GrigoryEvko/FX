8:2

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

If $p$ is parametric, its range of possible behaviors is considerably limited. Indeed, it cannot branch on concrete values of $X$ like $X = \text{Bool}$ and thus can only use its inputs $xs, ys$ through the List interface: the resulting list $p \ xs \ ys$ must be obtained by interleaving, duplicating or omitting values from $xs$ and $ys$. As a result, such a parametric program $p$ should satisfy the following theorem:

$$\forall (A_0 A_1 : \text{Type})(xs \ ys : \text{List } A_0)(f : A_0 \rightarrow A_1) \rightarrow \text{map } f \ (p \ xs \ ys) \equiv p \ (\text{map } f \ xs) \ (\text{map } f \ ys) \quad (2)$$

The theorem holds when $p$ is a list concatenation function, for instance. But in fact, the reasoning above applies for arbitrary parametric implementations of type $\forall \{X : \text{Type}\} \rightarrow \text{List } X \rightarrow \text{List } X \rightarrow \text{List } X$, which all satisfy the theorem. For this reason, the theorem is "free", i.e. obtained at zero cost.