# Chapter 14

## Cohesive parametric type theory

We develop a framework for cohesive parametric type theories following the pattern of definition first established in Chapter 3. In Section 14.1, we first define an interval theory, then give a notion of value type system that defines the value types and elements in each interval context. A value type system induces definitions of the closed judgments in the usual way. Up to this point, we are straightforwardly setting the theories of Parts I and III side by side, defining judgments $\Psi \Vdash M \in A \circledast m$ in each mode $m \in \{\text{par}, \text{pt}\}$.

The next step, taken in Section 14.2, is to extend the closed judgments to open judgments. It is easy enough to give the definition: an open judgment holds when it holds after any closing substitution. It is significantly more complicated to show that this definition satisfies the properties we need, as the forms of context are much more complex than in previous iterations. We spend Section 14.3 doing so. Everything flows from the need to formulate the rules for modal types, to which we finally arrive in Section 14.4. These motivate first modal context operators, then *endpoint hypotheses* and *modal hypotheses*.

**Context operators** As sketched in Chapter 13, we will have a context operator for each left adjoint of the cohesion situation and a modal type for each right adjoint, as in the following rules for $\text{Disc}(A)$.

$$\frac{\Gamma.\text{cc} \gg A \text{ type } \circledast \text{ pt}}{\Gamma \gg \text{Disc}(A) \text{ type } \circledast \text{ par}}$$

$$\frac{\Gamma.\text{cc} \gg M \in A \circledast \text{ pt}}{\Gamma \gg \text{mod}(M) \in \text{Disc}(A) \circledast \text{ par}}$$

Thus we must define three modal context operators. We write $-.\text{cc}$ for the connected components functor, $-.\text{dsc}$ for the discrete embedding, and $-.\text{glo}$ for global sections.

$$\frac{\Gamma \text{ ctx } \circledast \text{ par}}{\Gamma.\text{cc } \text{ctx } \circledast \text{ pt}}$$

$$\frac{\Gamma \text{ ctx } \circledast \text{ pt}}{\Gamma.\text{dsc } \text{ctx } \circledast \text{ par}}$$

$$\frac{\Gamma \text{ ctx } \circledast \text{ par}}{\Gamma.\text{glo } \text{ctx } \circledast \text{ pt}}$$

233