42

Martin-Löf's type theory

In a context like $\Gamma.C.B.A$, variables further back in the context are accessible by way of the projection substitution: we have $\Gamma.C.B.A \vdash v : A[p]$, $\Gamma.C.B.A \vdash v[p] : B[p \circ p]$, and $\Gamma.C.B.A \vdash v[p \circ p] : C[p \circ p \circ p]$. (Henceforth we write $p^2, p^3$, etc. for such iterated projections.) When we apply a substitution $\Gamma' \vdash \gamma.M : \Gamma.A$ into an extended context, the top variable $v$ is instantiated with $M$ by way of the first equation below, while other variables search deeper in the context via the second.

$$\frac{\Gamma' \vdash \gamma : \Gamma \qquad \Gamma \vdash A \text{ type} \qquad \Gamma' \vdash M : A[\gamma]}{\Gamma' \vdash v[\gamma.M] = M : A[\gamma]}$$

$$\frac{\Gamma' \vdash \gamma : \Gamma \qquad \Gamma \vdash A \text{ type} \qquad \Gamma' \vdash M : A[\gamma]}{\Gamma' \vdash p \circ (\gamma.M) = \gamma : \Gamma}$$

Note that the substitution pairing operator $-,-$ and the two projections $p$ and $v$ behave much like the constructor $\langle -, - \rangle$ and projections $fst$ and $snd$ of the dependent product type; intuitively, the extended context $\Gamma.A$ is the dependent product of $\Gamma$ and $A$. The uniqueness rule for products also has a counterpart.

$$\frac{\Gamma' \vdash \gamma : \Gamma.A \qquad \Gamma \vdash A \text{ type}}{\Gamma' \vdash \gamma = (p \circ \gamma).v[\gamma] : \Gamma.A}$$

The mechanical simplicity of nameless variables does unfortunately come at the cost of some readability, so we might be forgiven for using names and leaving the translation to $p$'s and $v$'s to the reader. We nevertheless stick to a nameless presentation, as such a translation becomes less evident in the presence of the new context formers (bridge interval extension and restriction, modalities) we introduce in Parts III and IV.

**Function types** Now that we have seen how to deal with variables in an algebraic fashion, the rules for function types contain no surprises. (Since there is no need to include a variable binding, we write $A \to B$ here even for dependent function types.)

$$\frac{\Gamma \vdash A \text{ type} \qquad \Gamma.A \vdash B \text{ type}}{\Gamma \vdash A \to B \text{ type}}$$

$$\frac{\Gamma.A \vdash N : B}{\Gamma \vdash \lambda(N) : A \to B}$$

$$\frac{\Gamma.A \vdash B \text{ type} \qquad \Gamma \vdash F : A \to B \qquad \Gamma \vdash M : A}{\Gamma \vdash FM : B[\text{id.}M]}$$

$$\frac{\Gamma.A \vdash N : B \qquad \Gamma \vdash M : A}{\Gamma \vdash \lambda(N)M = N[\text{id.}M] : B[\text{id.}M]}$$

$$\frac{\Gamma \vdash F : A \to B}{\Gamma \vdash F = \lambda(F[p]v) : A \to B}$$