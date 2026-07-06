11:58

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

To obtain the crisp induction principle we first use the ordinary one at mode $n$, and apply a number of modal combinators to bring it to mode $m$.

$$\begin{array}{l} \Gamma, \mathbf{\Theta}_{\nu} \vdash h \quad : (b : \mathbb{B}) \to \langle \mu \mid C(\mathrm{tt}) \rangle \to \langle \mu \mid C(\mathrm{ff}) \rangle \to \langle \mu \mid C(b^{\eta}) \rangle \circledast m \\ h(b, t, f) \quad \triangleq \mathrm{if}(b. \langle \mu \mid C(b^{\eta}) \rangle; t; f; b) \end{array}$$

$$\Gamma \vdash \mathrm{crisp\_if}_{C} \quad : (b : (\nu \mid \mathbb{B})) \to \langle \nu \circ \mu \mid C(\mathrm{tt}) \rangle \to \langle \nu \circ \mu \mid C(\mathrm{ff}) \rangle \to C^{\epsilon}(b) \circledast m$$

$$\mathrm{crisp\_if}_{C}(b, t, f) \triangleq \mathrm{counit}(\mathrm{mod}_{\nu}(h(b)) \circledast_{\nu} \mathbf{comp}_{\nu,\mu}^{-1}(t) \circledast_{\nu} \mathbf{comp}_{\nu,\mu}^{-1}(f))$$

The reasons why this term is well-typed is subtle. We have that $\Gamma, \mathbf{\Theta}_{\nu}, b : (1 \mid \mathbb{B}), \mathbf{\Theta}_{\mu \circ \nu} \vdash b^{\eta} : \mathbb{B} \circledast m$, so $\Gamma, \mathbf{\Theta}_{\nu}, b : (1 \mid \mathbb{B}), \mathbf{\Theta}_{\mu} \vdash C(b^{\eta}) \mathrm{type}_{1} \circledast n$ by the application rule. Thus, $h$ is well-typed. It remains to show that $C(b^{\eta})^{\epsilon} = C^{\epsilon}(b)$, which intuitively follows from the triangle identities. We may show it by precisely specifying what these operations mean in the algebraic syntax. First, we construct the substitutions

$$\sigma_{0} \triangleq \uparrow. \mathbf{\Theta}_{\mu}. \mathbf{v}_{0}[\mathbf{\Theta}_{\Gamma, \mathbf{\Theta}_{\nu}. (1 \mid \mathbb{B})}^{\eta}] : \Gamma. \mathbf{\Theta}_{\nu}. (1 \mid \mathbb{B}). \mathbf{\Theta}_{\mu} \to \Gamma. \mathbf{\Theta}_{\nu \circ \mu}. (\nu \mid \mathbb{B}) \circledast n$$

$$\sigma_{1} \triangleq \uparrow. \mathbf{\Theta}_{\nu}. \mathbf{v}_{0}. \mathbf{\Theta}_{\mu} \quad : \Gamma. (\nu \mid \mathbb{B}). \mathbf{\Theta}_{\nu \circ \mu} \to \Gamma. \mathbf{\Theta}_{\nu}. (1 \mid \mathbb{B}). \mathbf{\Theta}_{\mu} \circledast n$$

$$\sigma_{2} \triangleq (\mathbf{\Theta}_{\Gamma}^{\epsilon} \circ \uparrow). \mathbf{v}_{0} \quad : \Gamma. (\nu \mid \mathbb{B}) \to \Gamma. \mathbf{\Theta}_{\nu \circ \mu}. (\nu \mid \mathbb{B}) \circledast n$$

We can then interpret $C(b^{\eta})$ as the type $\Gamma. \mathbf{\Theta}_{\nu}. (1 \mid \mathbb{B}). \mathbf{\Theta}_{\mu} \vdash C[\sigma_{0}] \mathrm{type}_{1} \circledast n$. Similarly, $C(b^{\eta})^{\epsilon}$ is the type $\Gamma. (\nu \mid \mathbb{B}) \vdash C[\sigma_{0}][\sigma_{1}][\mathbf{\Theta}_{\Gamma, (\nu \mid \mathbb{B})}^{\epsilon}]$ $\mathrm{type}_{1} \circledast n$. Finally, $C^{\epsilon}(b)$ is the type $\Gamma. (\nu \mid \mathbb{B}) \vdash C[\sigma_{2}] \mathrm{type}_{1} \circledast n$, so it suffices to show that $\sigma_{0} \circ \sigma_{1} \circ \mathbf{\Theta}_{\Gamma, (\nu \mid \mathbb{B})}^{\epsilon} = \sigma_{2}$. This is a monstrous equation which is primarily structural. Moreover, $\eta$ occurs in $\sigma_{0}$, and $\epsilon$ in the key that follows it, so one of the triangle equations must somehow be implicated. Indeed, we can use one of the two equations along with the rules of Section 4 to prove the desired result.

We can now prove that

**Theorem 10.4.** $\langle \nu \mid \mathbb{B} \rangle \simeq \mathbb{B}$

*Proof.* We define the two functions

$$\begin{array}{l} \mathsf{b} \quad : \langle \nu \mid \mathbb{B} \rangle \to \mathbb{B} \circledast m \\ \mathsf{b}(x) \triangleq \mathrm{let} \ \mathrm{mod}_{\nu}(y) \leftarrow x \mathrm{in} \ \mathrm{crisp\_if}_{\mathbb{B}}(y, \mathrm{mod}_{\nu \circ \mu}(\mathrm{tt}), \mathrm{mod}_{\nu \circ \mu}(\mathrm{ff})) \\ \mathsf{b}^{-1} \quad : \mathbb{B} \to \langle \nu \mid \mathbb{B} \rangle \circledast m \\ \mathsf{b}^{-1} \triangleq \lambda x. \mathrm{if}(\_ \langle \nu \mid \mathbb{B} \rangle; \mathrm{mod}_{\nu}(\mathrm{tt}); \mathrm{mod}_{\nu}(\mathrm{ff}); x) \end{array}$$

We now use full crisp induction to construct for every $x : \langle \nu \mid \mathbb{B} \rangle$ a proof of $\mathrm{Id}_{\langle \nu \mid \mathbb{B} \rangle}(x, \mathsf{b}^{-1}(\mathsf{b}(x)))$. First, use modal induction to write $x = \mathrm{mod}_{\nu}(y)$ for some $y : (\nu \mid \mathbb{B})$. We then have to prove that $\mathrm{Id}_{\langle \nu \mid \mathbb{B} \rangle}(\mathrm{mod}_{\nu}(y), \mathsf{b}^{-1}(\mathsf{b}(\mathrm{mod}_{\nu}(y))))$, so we perform crisp induction on $y$. If $y \triangleq \mathrm{tt}$, we have that $\mathsf{b}^{-1}(\mathsf{b}(\mathrm{mod}_{\nu}(\mathrm{tt}))) = \mathrm{mod}_{\nu}(\mathrm{tt})$, so $\mathrm{mod}_{\nu \circ \mu}(\mathrm{refl}(\mathrm{mod}_{\nu}(\mathrm{tt})))$ has the right type. The case for $y \triangleq \mathrm{ff}$ is similar. The other direction is simpler, and follows by induction on $\mathbb{B}$. $\square$

Similar results hold for other types with 'positive,' 'pattern-matching,' or 'closed-scope' elimination rules. For example, we can also formulate a crisp induction principle for identity types, which can be used to prove that

**Theorem 10.5.** $\langle \nu \mid \mathrm{Id}_{A}(M_{0}, M_{1}) \rangle \simeq \mathrm{Id}_{\langle \nu \mid A \rangle}(\mathrm{mod}_{\nu}(M_{0}), \mathrm{mod}_{\nu}(M_{1}))$