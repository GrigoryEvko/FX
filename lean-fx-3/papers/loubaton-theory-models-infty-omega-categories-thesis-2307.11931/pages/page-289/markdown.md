5.2. CARTESIAN FIBRATIONS

Corollary 5.2.3.4. Let A be an  \( (\infty,\omega) \) -category. The inclusion  \( \mathrm{LCart}(A^{\sharp})\to(\infty,\omega)\text{-cat}_{\mathrm{m}/A^{\sharp}} \)  preserves both colimits and limits.

Proof. The preservation of limits is a consequence of the fact that that this inclusion is a right adjoint. The preservation of colimits is a direct consequence of the theorem 5.2.3.3. \(\square\)

5.2.3.5. We now use the last theorem to provide an alternative explicit expression of the left cartesian fibration  \( Fh_{[C,1]}^{0} \) . We obtain this in the theorem 5.2.3.10.

Proposition 5.2.3.6. Let C be an  \( (0,\omega) \) -category with an atomic and loop free basis. The canonical projection  \( \gamma:1\stackrel{\circ}{\star}C^{\flat}\to[C,1]^{\sharp} \)  is a left cartesian fibration.

Proof. Let C be such  \( (0,\omega) \) -category. The corollary 4.3.3.21, the theorem 4.3.3.5 and the proposition 4.3.3.2 imply that both the domain and the codomain of  \( \gamma \)  are strict. We can then show the result in  \( (0,\omega) \) -cat \( _{m} \) . By construction, the basis of  \( 1\stackrel{\circ}{\star}\lambda C \)  is given by the graduated set:

\[
(B _ {1 \stackrel {\circ} {\star} \lambda C}) _ {n} := \left\{ \begin{array}{l l} \{\emptyset^ {\stackrel {\circ} {\star}} c, c \in (B _ {C}) _ {0} \} \cup \{\emptyset^ {\stackrel {\circ} {\star}} c, c \in (B _ {C}) _ {0} \} & \text {if n = 0} \\ \{1 ^ {\stackrel {\circ} {\star}} c, c \in (B _ {C}) _ {n - 1} \} \cup \{\emptyset^ {\stackrel {\circ} {\star}} c, c \in (B _ {C}) _ {n} \} & \text {if n > 0} \end{array} \right.
\]

where \(B_{C}\) is the basis of \(C\). The derivative is induced by:

\[
\partial (1 \stackrel {\circ} {\star} c) := 1 \stackrel {\circ} {\star} \partial c + (- 1) ^ {| c |} \emptyset \otimes c \qquad \partial (\emptyset \star c) := \emptyset \stackrel {\circ} {\star} \partial c
\]

where we set the convention  \( \partial c := 0 \)  if  \( |c| = 0 \) . Let n be an integer and x an element of  \( (1 \stackrel{\circ}{\star} \lambda C)_n \) . The induced morphism  \( D_n \to 1 \stackrel{\circ}{\star} C^\flat \)  is marked if and only if there is no element of shape  \( \emptyset \star c \)  in the support of x.

For an integer \( n > 0 \), we define \( s_n: (\Sigma \lambda C)_n \to (1^{\circ} \star \lambda C)_n \) as the unique group morphism fulfilling

\[
s _ {n} (\Sigma c) := 1 \stackrel {\circ} {\star} c
\]

for \(c\) any element of \(\lambda C_{n - 1}\). Remark that for any non negative integer \(n\), and any element \(d\) of \((1^{\circ} \star \lambda C)_n\), \(s_n(d)\) is contained in \(d\). However, the family of morphism \(\{s_n\}_{n \in \mathbb{N}}\) does not commute with the derivative. Let \(n\) be an integer and \(x\) an element of \((1^{\circ} \star \lambda C)_n\). The induced morphism \(\mathbf{D}_n \to 1^{\circ} \star C^\flat\) is therefore marked if and only if \(x\) is equal to \(s_n \gamma_n(x)\).

Eventually, we recall that  \( (\mathbf{D}_{n})_{t} \otimes [1]^{\sharp} \)  is the colimit of the diagram:

\[
(\mathbf {D} _ {n}) _ {t} \otimes \{0 \} \coprod (\mathbf {D} _ {n}) _ {t} \otimes \{1 \} \longleftarrow \mathbf {D} _ {n} ^ {\flat} \otimes \{0 \} \coprod \mathbf {D} _ {n} ^ {\flat} \otimes \{1 \} \longrightarrow \tau_ {n} ^ {i} (\mathbf {D} _ {n} ^ {\flat} \otimes [ 1 ] ^ {\sharp})
\]

279