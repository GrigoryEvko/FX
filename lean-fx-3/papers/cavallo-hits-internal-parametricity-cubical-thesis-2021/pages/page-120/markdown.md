108

Case studies

of an indexed inductive type, implementing general coercion with a combination of formal coercion between indices and non-formal coercion between parameters. In the case of an inductive type with trivial indexing, this reduces to the non-formal coercion solution we have used so far. With this approach, the size of an inductive type is only dependent on the size of its indices, not its parameters: $\text{Id}(A, M_0, M_1)$ will be as large as $A$, this being the type of $M_0$ and $M_1$, but not as large as the type of $A$ (some U).

In the case of identity types, formal coercion takes the following form, allowing us to coerce between different instantiations of $M_0$ and $M_1$ but not of $A$.

$$\frac{A \text{ type} \quad x : \mathbb{I} \gg M_0, M_1 \in A \quad r, s \in \mathbb{I} \quad P \in \text{Id}(A, M_0[r/x], M_1[r/x])}{\text{fcoe}_{x,(M_0,M_1)}^{r \to s}(P) \in \text{Id}(A, M_0[s/x], M_1[s/x])}$$

As is our custom, we also impose the equation $\text{fcoe}_{x,(M_0,M_1)}^{r \to r}(P) = P$. Operationally, formal coercions are values unless trivial.

$$\frac{r \neq s}{\text{fcoe}_{x,(M_0,M_1)}^{r \to s}(P) \text{ val}} \quad \overline{\text{fcoe}_{x,(M_0,M_1)}^{r \to r}(P) \longmapsto P}$$

To implement general coercion, we combine formal index coercion with a parameter coercion operator implemented by case analysis, satisfying the following typing rule.

$$\frac{x : \mathbb{I} \gg A \text{ type} \quad M_0, M_1 \in A[r/x] \quad r, s \in \mathbb{I} \quad P \in \text{Id}(A[r/x], M_0, M_1)}{\text{pcoe}_{x,A \blacktriangleright \text{Id}}^{r \to s}(P) \in \text{Id}(A[s/x], \text{coe}_{x,A}^{r \to s}(M_0), \text{coe}_{x,A}^{r \to s}(M_1))}$$

In this case, we have a line $x.A$ in the type parameter, but indices $M_0, M_1$ only at the departure point $r$. These input indices are coerced along the parameter path $x.A$ in order to produce the indices for the output.

The general coercion operation is then derived by combining the parameter and index coercions: we first coerce to the correct parameters, then adjust the indices using a formal coercion.

$$\overline{\text{coe}_{x,\text{Id}(A,M_0,M_1)}^{r \to s}(P) \longmapsto \text{fcoe}_{x,(\text{coe}_{x,A}^{x \to s}(M_0), \text{coe}_{x,A}^{x \to s}(M_1))}^{r \to s}(\text{pcoe}_{x,A \blacktriangleright \text{Id}}^{r \to s}(P))}$$

To complete the picture, we just need to implement parameter coercion. For this, we follow the pattern of coercion in higher inductive types: evaluate the argument to a value and push the coercion inside. For identity types, there will be three types of values: refl terms, formal coercions, and formal composites. Note that despite the lack of explicit path constructors, formal composite values become necessary in order to ensure that the paths