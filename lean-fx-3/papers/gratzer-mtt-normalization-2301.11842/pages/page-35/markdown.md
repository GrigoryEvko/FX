Vol. 22:1

NORMALIZATION FOR MULTIMODAL TYPE THEORY

27:35

Proof. We show only the proof for this first claim. The 'only if' direction is established by the second point of Theorem 6.4. Suppose instead $\mathbf{nf}_{\Gamma}(M, A) = \mathbf{nf}_{\Gamma}(N, A)$, so $|\mathbf{nf}_{\Gamma}(M, A)| = |\mathbf{nf}_{\Gamma}(N, A)|$. By the first point of Theorem 6.4, $|\mathbf{nf}_{\Gamma}(M, A)| = M$ and $|\mathbf{nf}_{\Gamma}(M, A)| = N$, so the conclusion follows.

A priori, however, a given term could have multiple normal forms which complicates further analysis. We therefore strengthen Theorem 6.4 with the following:

# **Theorem 6.7** (Tightness).

(1) If $\Gamma \vdash^{\mathrm{nf}} u : A \circledast m$, then $\mathbf{nf}_{\Gamma}(|u|, A) = u$.
(2) If $\Gamma \vdash^{\mathrm{nf}} \tau \circledast m$, then $\mathbf{nfty}_{\Gamma}(|\tau|) = \tau$.

Proof. Recall that Theorems 3.9 and 5.12 induce a function $[[-]$ sending a piece of syntax to its interpretation in the normalization model. Furthermore, recall the $\Gamma$-element $\mathsf{atoms}_{\Gamma} : [\Gamma]$ constructed in Lemma 6.2.

We begin by strengthening the statement to make it more amenable to induction:

(1) If $\Gamma \vdash^{\mathrm{pe}} e : A \circledast m$, then $[[M]](\mathsf{atoms}_{\Gamma}) = \uparrow_{[A](\mathsf{atoms}_{\Gamma})} e$
(2) If $\Gamma \vdash^{\mathrm{nf}} u : A \circledast m$, then $\downarrow_{[A](\mathsf{atoms}_{\Gamma})} [[u]](\mathsf{atoms}_{\Gamma}) = u$.
(3) If $\Gamma \vdash^{\mathrm{nf}} \tau \circledast m$, then $[[A]].\mathsf{code}(\mathsf{atoms}_{\Gamma}) = \tau$.

Here we have identified a code $u$ (resp. $e$) as an $\Gamma$-element of $\mathsf{Nf}_A$ (resp. $\mathsf{Ne}_A$). All three follow straightforwardly from mutual induction and the relevant definitions. For instance, if we consider $\Gamma \vdash^{\mathrm{nf}} (\mu \mid \tau) \to \sigma \circledast m$, we calculate as follows:

$$\begin{array}{l} [ [ (\mu \mid \tau) \to \sigma ] ].\mathsf{code}(\mathsf{atoms}_{\Gamma}) \\ = [ [ (\mu \mid |\tau|) \to |\sigma| ].\mathsf{code}(\mathsf{atoms}_{\Gamma}) \\ = (\mu \mid [ [\tau] ].\mathsf{code}(\mathsf{atoms}_{\Gamma})) \to [ [\sigma] ].\mathsf{code}(\uparrow^*\mathsf{atoms}_{\Gamma}, \uparrow \mathbf{v}_0) \\ = (\mu \mid [ [\tau] ].\mathsf{code}(\mathsf{atoms}_{\Gamma})) \to [ [\sigma] ].\mathsf{code}(\mathsf{atoms}_{\Gamma,(\mu|A)}) \\ = (\mu \mid \tau) \to \sigma \end{array}$$

In order to carry out this calculation, we took advantage of not only the definition of dependent products in the gluing model, but also the interpretation of HOAS and atoms.

**Corollary 6.8.** *Normalization is an isomorphism between equivalence classes of terms (resp. types) and normal forms (resp. normal types).*

Proof. Corollary 6.6 already shows that normalization is injective and Theorem 6.7 provides a section.

These results imply the injectivity of type constructors, an essential property for implementation.

**Corollary 6.9.** *If $\Gamma \vdash A_0 \to B_0 = A_1 \to B_1 \circledast m$ then $\Gamma \vdash A_0 = A_1 \circledast m$ and $\Gamma.(\mathsf{id} \mid A_0) \vdash B_0 = B_1 \circledast m$.*

Proof. Set $\tau_i = \mathbf{nfty}_{\Gamma}(A_i)$ and $\sigma_i = \mathbf{nfty}_{\Gamma.(\mathsf{id}|A_0)}(B_i)$. Unfolding definitions shows that $|(\mu \mid \tau_i) \to \sigma_i| = |\tau_i| \to |\sigma_i| = A_i \to B_i$. By Corollary 6.8, $\mathbf{nfty}_{\Gamma}(A_i \to B_i) = (\mu \mid \tau_i) \to \sigma_i$.

Next, we recall that $\Gamma \vdash A_0 \to B_0 = A_1 \to B_1 \circledast m$ by assumption, so $(\mu \mid \tau_0) \to \sigma_0 = (\mu \mid \tau_1) \to \sigma_1$. As an operation on normal forms, however, $(\mu \mid -) \to -$ is clearly injective, so $\tau_0 = \tau_1$ and $\sigma_0 = \sigma_1$. The result now follows from Corollary 6.6.