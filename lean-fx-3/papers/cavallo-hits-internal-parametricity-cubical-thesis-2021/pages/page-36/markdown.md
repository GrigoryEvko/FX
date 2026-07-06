24

Martin-Löf's type theory

**Symmetry and transitivity** We warm up by proving symmetry and transitivity of the binary judgments, which follow more or less immediately from the corresponding properties of the value type system. It is convenient to first prove the rules for the closed judgments, then extend them uniformly to the open judgments.

**Rules 2.1.13 (Symmetry and transitivity for closed judgments).**

$$\Vdash A = B \text{ type}$$

$$\Vdash B = A \text{ type}$$

$$\Vdash A = B \text{ type} \quad \Vdash B = C \text{ type}$$

$$\Vdash A = C \text{ type}$$

$$\Vdash M = N \in A$$

$$\Vdash N = M \in A$$

$$\Vdash M = N \in A \quad \Vdash N = P \in A$$

$$\Vdash M = P \in A$$

*Proof.* Consider first the symmetry of the typing judgment. By definition of $\Vdash A = B$ type, our assumption is that $A \Downarrow A_0$ and $B \Downarrow B_0$ for some values $A_0, B_0$ and $\tau \vDash A_0 \approx B_0 \downarrow R$ for some $R$. By symmetry of the value type system, it follows that $\tau \vDash B_0 \approx A_0 \downarrow R$ and thus that $\Vdash B = A$ type.

For transitivity, $\Vdash A = B$ type tells us that $A \Downarrow A_0$ and $B \Downarrow B_0$ with $\tau \vDash A_0 \approx B_0 \downarrow R$, while $\Vdash B = C$ type tells us that $B \Downarrow B'_0$ and $C \Downarrow C_0$ with $\tau \vDash B'_0 \approx C_0 \downarrow R'$. By determinism of the type system, we know that $B_0 = B'_0$. Applying symmetry and transitivity of the value type system, we can conclude that $\tau \vDash B_0 \downarrow R$ and $\tau \vDash B_0 \downarrow R'$; thus $R = R'$ by unicity. Finally, transitivity of the value type system now applied with $\tau \vDash A_0 \approx B_0 \downarrow R$ and $\tau \vDash B_0 \approx C_0 \downarrow R$ gives the result.

Symmetry and transitivity for terms follow by similar arguments, this time using the fact that the relations returned by a value type system are always PERs. $\square$

**Rules 2.1.14 (Symmetry and transitivity for closing substitutions).**

$$\Gamma \text{ ctx} \quad \Vdash \gamma = \gamma' \in \Gamma$$

$$\Vdash \gamma' = \gamma \in \Gamma$$

$$\Gamma \text{ ctx} \quad \Vdash \gamma = \gamma' \in \Gamma \quad \Vdash \gamma' = \gamma'' \in \Gamma$$

$$\Vdash \gamma = \gamma'' \in \Gamma$$

*Proof.* By induction on the defining rules for closing substitutions and Rules 2.1.13. $\square$

**Rules 2.1.15 (Symmetry and transitivity for open judgments).**

$$\Gamma \text{ ctx} \quad \Gamma \gg A = B \text{ type}$$

$$\Gamma \gg B = A \text{ type}$$

$$\Gamma \text{ ctx} \quad \Gamma \gg A = B \text{ type} \quad \Gamma \gg B = C \text{ type}$$

$$\Gamma \gg A = C \text{ type}$$

$$\Gamma \text{ ctx} \quad \Gamma \gg M = N \in A$$

$$\Gamma \gg N = M \in A$$

$$\Gamma \text{ ctx} \quad \Gamma \gg M = N \in A \quad \Gamma \gg N = P \in A$$

$$\Gamma \gg M = P \in A$$