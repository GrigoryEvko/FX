Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:41

TRANSP:ELIM

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma \text{ctx}\)

\(\mathbb{X} \mid \Gamma, \widehat{\mathbb{Q}}_u^{\forall u} \vdash A \text{type}\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, r: \langle \langle \langle u \mid A \rangle \vdash C \text{type}\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, -: u \in \partial \mathbb{U} \vdash c_{\text{pole}}: C[\text{pole}/r]\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, \widehat{\mathbb{Q}}_u^{\forall u}, x: A, \widehat{\mathbb{Q}}_u^{\exists [u]} \vdash c_{\text{mer}}: C[\text{id}_\Gamma, \widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}, \text{mod}_{\langle [u]} (x_{\text{unmer}_u^{-1}}^ {-1})/r]\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma, \widehat{\mathbb{Q}}_u^{\forall u}, x: A, \widehat{\mathbb{Q}}_u^{\exists [u]}, -: u \in \partial \mathbb{U} \vdash c_{\text{mer}} = c_{\text{pole}}[\text{id}_\Gamma, \widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}]: C[\text{id}_\Gamma, \widehat{\mathbb{Q}}_{\text{reidx}_u}^{\text{app}_u}, \text{pole}/r]\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma \vdash t: \langle \langle [u] | A\rangle\)

\(\mathbb{X}, u: \mathbb{U} \mid \Gamma \vdash c := \text{case } t \text{ of } \{\text{pole} \mapsto c_{\text{pole}} | \text{mer } x \mapsto c_{\text{mer}}\}: C[t/r]\)

where \(c[\text{pole}/t] = c_{\text{pole}}\)

\(\mathbb{X}, u: \mathbb{U} \mid \Delta, \widehat{\mathbb{Q}}_u^{\exists [u]} \vdash c = c_{\text{mer}}[\text{id}_\Delta, \widehat{\mathbb{Q}}_{\text{unmer}_u}^{\text{const}_u}, \text{unmer}_u \sim_{\forall u} t/x, \widehat{\mathbb{Q}}_u^{\exists [u]}]: C\)

Figure 8: Transpension elimination by pattern matching (sound if U is T-slice fully faithful and shard-free). Recall Eq. (3.1).

presheafwise) fully faithful, then the applied locks are actually isomorphic to the identity lock (Theorem 6.31). In any case, regardless of the properties of U, Proposition 3.3 tells us that the let-rule for  \( \langle[u:U] \)  has the same power as

\[
\operatorname{unmer} _ {u}: (\forall (u: \mathbb {U}) \mid \langle \langle [ u: \mathbb {U} ] \mid T \rangle) \rightarrow T [ \widehat {\mathbf {Q}} _ {\text { unmer } _ {u}} ^ {\text { const } _ {u}} ]
\]

which extracts meridians. If U is T-slice fully faithful, then the 2-cell unmer \( _{u} \) is invertible (Theorem 6.31) and we can also straightforwardly create meridians from elements of \( T[\widehat{\mathbf{Q}}_{\text{unmer}_{u}}^{\text{const}_{u}}] \).

9.3. Pattern matching. The eliminator  \( unmer_{u} \)  is only capable of eliminating sections of the transpension type. If the quotient Theorem 6.28 applies to U, we can eliminate locally by pattern matching:

Theorem 9.3. If U is T-slice (hence presheafwise) fully faithful and shard-free, then the rule TRANSP:ELIM in Fig. 8 is sound [Nuy20b].

The elimination rule is best understood by looking at the left names. We get a context \(\Gamma\) depending on \(u: \mathbb{U}\), a type \(A\) depending on sections of \(\Gamma\) (as represented by \(\Gamma, \widehat{\mathbb{Q}}_u^{\forall u}\)), a type \(C\) depending on \(u\) and \(r: \langle \langle [u] | A \rangle\), and an argument \(t\) of type \(\langle [u] | A \rangle\). To obtain a value of type \(C\), we need to give an action \(c_{\text{pole}}\) on the boundary, where \(t\) is necessarily pole (pole Theorem 9.1), and a compatible action on sections of the transpension type, i.e. meridians, which live over sections of \(\Gamma\) but are themselves essentially elements of \(A\) (quantification Theorem 6.31), producing sections of \(C\) (but the quantifier \(\forall u\) has been brought to the left as \(\widehat{\mathbb{Q}}_u^{\exists [u]}\)). Thanks to shard-freedom, we know that everything that is not a section\(^{21}\), is on the boundary, so this suffices.

The computation rule for meridians fires when all of \(\Gamma\) is fresh for \(u\). In this situation, the judgement for \(t\) is \(\mathbb{X}, u: \mathbb{U} \mid \Delta, \widehat{\mathbb{Q}}_u^{\exists [u]} \vdash t: \langle \langle [u] \mid A \rangle\) which by transposition boils down to \(\mathbb{X} \mid \Delta \vdash t': \langle \forall a \mid \langle [u] \mid A \rangle \rangle\), i.e. it fires when \(t\) can actually be seen as a full section of the transpension type, so that we can apply the action on sections given by \(c_{\mathrm{mer}}\).

\( ^{21} \) or a ‘dimensional section’ in case of base categories that are not objectwise pointable