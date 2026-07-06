Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:11

and

$$\begin{array}{l} \mathbf {c o m p} _ {\mu , \nu} ^ {- 1}: \langle \mu \circ \nu \mid A \rangle \rightarrow \langle \mu \mid \langle \nu \mid A \rangle \rangle \\ \mathbf {c o m p} _ {\mu , \nu} ^ {- 1} (x) \triangleq \operatorname {l e t} \operatorname {m o d} _ {\mu \circ \nu} \left(x _ {0}\right) \leftarrow x \text {i n} \operatorname {m o d} _ {\mu} \left(\operatorname {m o d} _ {\nu} \left(x _ {0}\right)\right) \end{array}$$

We elide the 2-cell annotations on variables, as they are all identities (i.e. we only need TM/VAR/COUNT). Even in this small example the context equations for locks are essential: for $\langle \mu \mid \langle \nu \mid A \rangle \rangle$ to be a valid type we need that $\Gamma, \mathbf{\Omega}_{\mu}, \mathbf{\Omega}_{\nu} = \Gamma, \mathbf{\Omega}_{\mu \circ \nu}$, which is ensured by CX/COMPOSE. Furthermore, observe that $\mathbf{comp}_{\mu,\nu}$ crucially relies on the multimodal elimination rule TM/MODAL-ELIM: we must pattern-match on $x_0$, which is under $\mu$ in the context.

Similarly, fixing $\Gamma \vdash A$ type$_1$ @ $m$ we have

$$\mathbf {t r i v} (-): \langle 1 \mid A \rangle \rightarrow A \quad \mathbf {t r i v} ^ {- 1} (-): A \rightarrow \langle 1 \mid A \rangle$$

$$\mathbf {t r i v} (x) \triangleq \operatorname {l e t} \operatorname{mod} _ {1} (x _ {0}) \leftarrow x \text {i n} x _ {0} \quad \mathbf {t r i v} ^ {- 1} (x) \triangleq \operatorname{mod} _ {1} (x)$$

In both cases, these combinators are only propositionally inverse. For example, the proof for one direction of the composition combinator is

$$\begin{array}{l} \_ : (x: \langle \mu \mid \langle \nu \mid A \rangle \rangle) \rightarrow \operatorname{Id} _ {\langle \mu | \langle \nu | A \rangle \rangle} (x, \mathbf {c o m p} _ {\mu , \nu} ^ {- 1} (\mathbf {c o m p} _ {\mu , \nu} (x))) \\ \_ \triangleq \lambda x. \operatorname {l e t} \operatorname{mod} _ {\mu} (x _ {0}) \leftarrow x \text {i n} \operatorname {l e t} _ {\mu} \operatorname{mod} _ {\nu} (x _ {1}) \leftarrow x _ {0} \text {i n} \operatorname{refl} (\operatorname{mod} _ {\mu} (\operatorname{mod} _ {\nu} (x))) \end{array}$$

This is in many ways a typical example: we use the modal elimination rule to induct on a modally-typed term, which reduces it to a term of the form mod(-). This is just enough to make various terms compute, and the result then follows by reflexivity.

As a final example, we will show that each modal type satisfies the $K$ axiom,$^1$ a central axiom of Kripke-style modal logics. This combinator will be immediately recognizable to functional programmers: it is the term that witnesses that $\langle \mu \mid -\rangle$ is an applicative functor [MP08].

$$\begin{array}{l} - \circledast_ {\mu} -: \langle \mu \mid A \rightarrow B \rangle \rightarrow \langle \mu \mid A \rangle \rightarrow \langle \mu \mid B \rangle \\ f \circledast_ {\mu} a \triangleq \operatorname {l e t} \operatorname{mod} _ {\mu} (f _ {0}) \leftarrow f \text {i n} \operatorname {l e t} \operatorname{mod} _ {\mu} (a _ {0}) \leftarrow a \text {i n} \operatorname{mod} _ {\mu} (f _ {0} (a _ {0})) \end{array}$$

We can also define a stronger combinator which corresponds to a dependent form of the Kripke axiom [BCM$^+$20] along the same lines. As it generalizes $\circledast_{\mu}$ to dependent products, this operation has precisely the same implementation but a more complex type:

$$\langle \mu \mid (x: A) \rightarrow B \rangle \rightarrow (x _ {0}: \langle \mu \mid A \rangle) \rightarrow (\operatorname {l e t} \operatorname{mod} _ {\mu} (x) \leftarrow x _ {0} \text {i n} \langle \mu \mid B \rangle)$$

In order to ensure that $\langle \mu \mid B \rangle$ is well-typed, the context must contain $x: (\mu \mid A)$, but instead we have bound $x_0: (1 \mid \langle \mu \mid A \rangle)$. We correct this mismatch by eliminating $x_0$ and binding the result to $x$.

3.2. Idempotent Comonads in MTT. A great deal of prior work in modal type theory has focused on comonads [PD01, dR15, Shu18, GSB19a], and in particular idempotent comonads. [Shu18, Theorem 4.1] has shown that such modalities necessitate changes to the judgmental structure, as the only idempotent comonads that are internally definable in type theory are of the form $- \times U$ for some proposition $U$. In this section we present a mode theory for idempotent comonads, and prove that the resulting type theory internally satisfies the expected equations. In fact, we only use the combinators of the previous section.

We define the mode theory $\mathcal{M}_{\mathrm{ic}}$ to consist of a single mode $m$, and a single non-trivial morphism $\mu : m \to m$. We will enforce idempotence by setting $\mu \circ \mu = \mu$. Finally, in order

$^1$Not to be confused with Streicher's axiom $K$.