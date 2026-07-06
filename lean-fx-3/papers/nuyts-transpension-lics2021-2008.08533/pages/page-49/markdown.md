Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:49

Note that for general multipliers, $\mathbb{J}[i]$ does not have an internal left adjoint and hence not a modal projection function either. For the nullary affine interval, however, $\mathbb{J}[i] \cong \mathbb{Q}[i]$, so the projection function is essentially unmer$_{i}$!

Example 10.4. Consider Pitts's implementation of higher dimensional pattern matching [Pit14]:

$$j : (\mathsf{M}[i : N].A \uplus B) \to (\mathsf{M}[i : N].A) \uplus (\mathsf{M}[i : N].B)$$

$$j \, \hat{c} = \nu[i : N].\text{case } \hat{c}@i \text{ of } \left\{ \begin{array}{l l l} \text{inl } a & \mapsto & \text{inl } (\langle i : N \rangle . a) \\ \text{inr } b & \mapsto & \text{inr } (\langle i : N \rangle . b) \end{array} \right\}$$

A brainless translation using Fig. 12 yields a type mismatch, because the non-binding abstractions will put the freshness constructor inside the coproduct constructors, whereas the translation of the locally fresh name abstraction mentions it again on the outside. This is related to our earlier remark that in FreshMLTT, freshness silently propagates through type and term constructors, so here we have to manually intervene. This is also necessary to insert invertible 2-cell substitutions in some places, and to check whether we need a modal argument (i.e. the modality is handled at the judgemental level) or we need to explicitly use the modal constructor as is always done in Fig. 12. Doing so, we find

$$j : \langle \mathsf{M} \, i \mid A \uplus B \rangle \to \langle \mathsf{M} \, i \mid A \rangle \uplus \langle \mathsf{M} \, i \mid B \rangle$$

$$j \, \hat{c} = \text{drop}_i \cdot_{\mathsf{M} \, i} \text{case } (\text{app}_i \cdot_{\mathbb{J}[i]} (\hat{c}_{\text{const}_i}^{\text{drop}_i})) \text{ of } \left\{ \begin{array}{l} \text{inl } a \mapsto \text{mod}_{\mathbb{J}[i]} (\text{inl } (\text{mod}_{\mathsf{M} \, i} (a_{\text{copy}_i}^{\text{app}_i}))) \\ \text{inr } b \mapsto \text{mod}_{\mathbb{J}[i]} (\text{inr } (\text{mod}_{\mathsf{M} \, i} (b_{\text{copy}_i}^{\text{app}_i}))) \end{array} \right\},$$

which is exactly what we found in Section 7.3 adapted to our convention that we only want to mention $\mathbb{J}[i]$ and $\forall \, i$, $\text{app}_i$, $\text{copy}_i$, $\text{const}_i$ and $\text{drop}_i$.

Example 10.5. Consider Pitts et al.'s implementation [PMD15, ex. 2.2] of what is essentially BCM's $\Phi$-rule [Mou16, BCM15] since the boundary is empty:

$$g : ((\mathsf{M}[i : N].A) \to \mathsf{M}[i : N].B) \to \mathsf{M}[i : N].(A \to B)$$

$$g \, f = \alpha[i : N].(\lambda x. f \, (\langle i : N \rangle . x) \, @ \, i.$$

We can translate this to the current system using Fig. 12:

$$g : (\langle \mathsf{M} \, i \mid A \rangle \to \langle \mathsf{M} \, i \mid B \rangle) \to \langle \mathsf{M} \, i \mid A \to B \rangle$$

$$g \, f = \text{mod}_{\mathsf{M} \, i} \left( \lambda x. \text{app}_i \cdot_{\mathbb{J}[i]} (f[\mathbf{a}_{\text{const}_i}^{\text{drop}_i}] (\text{mod}_{\mathsf{M} \, i} (x_{\text{copy}_i}^{\text{app}_i}))) \right).$$

The effect of conflating $\mathbf{a}_{\mathbb{J}[i]}^{\exists \, i}$ with $\mathbf{a}_{\mathbb{J}[i]}^{\forall \, i}$ is that affine function application no longer renders the non-fresh part of the context inaccessible using $\mathbf{a}_{\mathbb{J}[i]}^{\exists \, i}$ but instead universally quantifies it using $\mathbf{a}_{\mathbb{J}[i]}^{\forall \, i}$, so that we can capture variables as in FreshMLTT. Remarkably, we do not need the $\Phi$-rule (Fig. 10) for this nor pattern-matching for the transpension type (Fig. 8), although these rules hold as the affine cubical interval is $\top$-slice fully faithful and shard-free (Example 6.14).

## 11. CONCLUSION

To summarize, the transpension type can be defined in a broad class of presheaf models and generalizes previous internalization operators. For now, we only present an extensional type system without an algorithmic typing judgement. The major hurdles towards producing an intensional version with decidable type-checking, are the following: