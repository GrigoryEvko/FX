Formalism and models 77

Finally, we have the crucial univalence principle relating paths between types in the universe U to isomorphisms between those types. Note that by the above, we need only prove that the types $A \simeq B$ are retracts of the types $\text{Path}(U, A, B)$.

**Theorem 3.2.9 (Univalence).** Let $A, B \in U$. Then the following function from paths in U to isomorphisms is an isomorphism.

$$\lambda p. \text{coe}_{x.p.x}^{0=1} \in \text{Path}(U, A, B) \rightarrow (A \simeq B)$$

*Proof.* From [Ang19, Theorem 4.105] via Lemma 3.2.8 and [Uni13, Theorem 4.3.2], the last of which shows that isomorphisms are path-equal whenever their underlying forward functions are path-equal. $\square$

### 3.3 Formalism and models

The cubical type theory $\tau_1$ interprets most of the constructs of the **ITT** formalism sketched in Section 2.2, with the notable exception of identity types (which we have replaced with path types). In Section 5.3 of Part II, we describe one way to recover identity types in a cubical setting. With that lacuna patched, we will be able interpret **ITT** as well as the univalence axiom; using the higher inductive types also constructed in Part II, we can obtain a computational interpretation of **HoTT**.

Alternatively, we may abandon identity types and **HoTT** entirely and instead develop a natively cubical formalism. This approach has some notable benefits. For one, **HoTT** is lacking as a formalism from a computational standpoint, failing to satisfy any kind of adequacy theorem (Proposition 2.2.1) thanks to its lack of rules for reducing applications of univalence and higher inductive type eliminators. This makes it difficult to use **HoTT** to prove calculational results. Indeed, cubical type theory has an advantage in usability more broadly. This observation goes back to Licata and Brunerie, who showed that merely adopting a cubical organization for arguments in **HoTT** could drastically simplify proofs [LB15]. (My own master's thesis [Cav15] owes a tremendous debt to that observation.) The effect is even more pronounced in a natively cubical theory, as many of the rules which hold only up to identity in **HoTT** are exact in cubical type theory. The formulation of path equality as function-like also means that the characterization of paths in compound negative types is very straightforward, as in the proofs of Lemmas 3.2.4 and 3.2.5 above.

We can straightforwardly adjust the formalism for intensional type theory introduced in Section 2.2 to expose cubical elements. We add judgments for two new concepts: the interval and constraints.