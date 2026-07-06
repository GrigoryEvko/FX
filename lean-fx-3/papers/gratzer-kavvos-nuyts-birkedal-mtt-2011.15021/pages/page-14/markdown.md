11:14

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

$$\begin{array}{r} \boxed{\Gamma \text{ ctx } @ m} \\ \hline \cdot \text{ ctx } @ m \qquad \frac{\Gamma \text{ ctx } @ m \qquad \mu : \text{Hom}_{\mathcal{M}}(n, m)}{\Gamma \widehat{\bullet}_{\mu} \text{ ctx } @ n} \\ \frac{\Gamma \text{ ctx } @ m \qquad \mu : \text{Hom}_{\mathcal{M}}(n, m) \qquad \Gamma \widehat{\bullet}_{\mu} \vdash A \text{ type}_1 @ n}{\Gamma (\mu \mid A) \text{ ctx } @ m} \\ \frac{\Gamma \text{ ctx } @ m \qquad \nu : \text{Hom}_{\mathcal{M}}(o, n) \qquad \mu : \text{Hom}_{\mathcal{M}}(n, m)}{\Gamma \widehat{\bullet}_{\mu} \widehat{\bullet}_{\nu} = \Gamma \widehat{\bullet}_{\mu \circ \nu} \text{ ctx } @ o} \qquad \frac{\Gamma \text{ ctx } @ m}{\Gamma \widehat{\bullet}_1 = \Gamma \text{ ctx } @ m} \end{array}$$

Figure 3: MTT Contexts

Even though we will use this more familiar notation, we will take no prisoners in terms of rigour: we will carefully avoid overloading and ambiguity, and we will enforce presupposition.

4.2. Judgments. We shall now introduce the type theory itself by writing down the constructors and equalities of its GAT. In the interest of brevity, we elide a number of standard rules, including

- the congruence rules pushing substitutions inside terms and types;
- the congruence rules pushing explicit lifts inside of type formers;
- the associativity, unit, and weakening laws for the explicit substitutions;
- the $\beta$ laws for $\Pi$, $\Sigma$, $\mathbb{B}$ and $\text{Id}$;
- the $\eta$ laws for $\Pi$ and $\Sigma$;

The specification of the GAT is given in Figures 3–9. As the judgments are defined in a mutually recursive manner, the division of the rules between different figures is merely presentational. Given $\Delta \vdash \gamma : \Gamma @ m$ and $\Gamma \widehat{\bullet}_{\mu} \vdash A \text{ type}_\ell @ m$ we write

$$\Delta (\mu \mid A [\gamma \widehat{\bullet}_{\mu}]) \vdash \gamma^+ \triangleq (\gamma \circ \uparrow) \cdot \mathbf{v}_0 : \Gamma (\mu \mid A) @ m$$

for the 'weakened' substitution.

4.3. Discussion. We record some points on the generalized algebraic theory.

Modal dependent products. The algebraic presentation of MTT includes a primitive modal dependent product type $(\mu \mid A) \rightarrow B$. This is a combination of the modality $\langle \mu \mid - \rangle$ and the ordinary dependent product. Using a named syntax, it may be understood as

$$(x : (\mu \mid A)) \rightarrow B \triangleq (x_0 : \langle \mu \mid A \rangle) \rightarrow (\text{let } \text{mod}_\mu(x) \leftarrow x_0 \text{ in } B)$$

However, the modal types of MTT do not readily support a definitional $\eta$-equality, so this definition is not equivalent to the modal dependent product of the GAT. We use the latter because it is convenient for programming, and also has a natural semantics, which we will present in Section 5.2.1.