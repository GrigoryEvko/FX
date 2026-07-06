146

General higher inductive types

Proof. By induction on the derivation of $\Psi' \Vdash \Delta\psi \mid \mathcal{K}\psi \blacktriangleright \Theta = \Theta'$ actx. In the case of a non-empty context, well-typedness of act follows by induction on the argument type, using (trivial) coherent expansion in each case in accordance with the operational semantics shown in Figure 6.7. $\square$

We moreover need to know that the action of argument contexts commutes with argument substitution in an appropriate sense, as captured by the following definition.

Definition 6.4.12. We say that a term $\overline{v}_{\Delta}.h.T$ commutes with substitution interpretation below $n$ when for every $\Psi' \Vdash \psi \in \Psi$, argument substitution $\Psi' \Vdash \Delta\psi \mid \mathcal{K}\psi \mid \Theta' \blacktriangleright \theta \in \Theta$ with $|\Theta'|_{\mathcal{K}}, |\Theta|_{\mathcal{K}}, |\theta|_{\mathcal{K}} < n$, and $\chi \in \{\Theta'\}_{\mathcal{K}}(Elim^{-1})$, we have

$$\Psi' \Vdash \overline{\mathrm{act}}(\Theta; \overline{v}_{\Delta}.h.T\psi; \langle\theta\rangle_{\mathcal{K}\psi}(\chi)) = \langle\theta\rangle_{\overline{v}_{\Delta}.h.D\psi}^{\mathcal{K}\psi,\mathcal{E}\psi}(\chi; \overline{\mathrm{act}}(\Theta'; \overline{v}_{\Delta}.h.T\psi; \chi))$$

at the type $\langle\Theta\rangle_{\mathcal{K}\psi,\mathcal{E}\psi}^{\overline{v}_{\Delta}.h.D\psi}(\langle\theta\rangle_{\mathcal{K}\psi}(\chi))$.

Lemma 6.4.13 (Naturality). If $Intro_{\ell}^{\mathcal{K}}(Elim^{-1}) \subseteq Elim^{-1}$ for all $\ell$ with $|\ell|_{\mathcal{K}} < n$, then $\mathrm{elim}(\overline{v}_{\Delta}.h.D; -; -; \mathcal{E})$ commutes with substitution interpretation below $n$.

Proof. By induction on the derivation of $\Psi' \Vdash \Delta\psi \mid \mathcal{K}\psi \mid \Theta' \blacktriangleright \theta \in \Theta$ in the definition of Definition 6.4.12. $\square$

Remark 6.4.14. There are reasonable extensions to the argument term language that would invalidate Lemma 6.4.13. It depends in particular on the fact that the argument type formers are all negative, satisfying uniqueness principles up to exact equality. If these were positive—like inductive types—the property would instead hold only up to a path. We expect it would still be possible, although certainly more complicated, to define the eliminator by including “correction” composites in the reduction rules for path constructors as we do in coercion.

Lemma 6.4.15 (Reduction of elim on intro). Let $\ell \in \mathcal{K}$. Suppose that the eliminator $\mathrm{elim}(\overline{v}_{\Delta}.h.D; -; -; \mathcal{E})$ commutes with substitution interpretation below $|\ell|_{\mathcal{K}}$. Then the following rule is validated for any $\Psi' \Vdash (\psi, \delta) \in (\Psi, \Delta)$.

$$\begin{array}{l} (\ell : \Phi.\Omega.[\delta'; \Theta.\overline{\xi_i \hookrightarrow \mathrm{M}_i}]) \in \mathcal{K}\psi \quad \Psi' \Vdash \Delta\psi \blacktriangleright \mathcal{K}\psi = \mathcal{K}'' \text{ spec} \\ \Psi' \Vdash \phi \in \Phi \quad \Psi' \Vdash \omega \in \Omega\phi \quad \Psi' \Vdash \delta'[\phi, \omega] = \delta \in \Delta\psi \\ \chi \in \Downarrow \{\Theta[\phi, \omega]\}_{\mathcal{K}}(Elim^{-1}\psi) \quad \rho := \overline{\mathrm{act}}(\Theta; \overline{v}_{\Delta}.h.\mathrm{elim}(\overline{v}_{\Delta}.h.D\psi; \delta; h; \mathcal{E}\psi); \chi) \\ \mathrm{H} := (\Phi, \Omega, \langle\Theta\rangle_{\mathcal{K}\psi}^{\Delta\psi}, \langle\Theta\rangle_{\mathcal{K}\psi,\mathcal{E}\psi}^{\Delta.h.D\psi}(\overline{v}_{\langle\Theta\rangle_{\mathcal{K}\psi}^{\Delta\psi}})) \quad (\ell : \overline{v}_{\mathrm{H}}.T) \in \mathcal{E}\psi \end{array}$$

$$\overline{\Psi' \Vdash \mathrm{elim}(\overline{v}_{\Delta}.h.D\psi; \delta; \mathrm{intro}_{\ell}^{\mathcal{K}''}(\phi; \omega; \chi); \mathcal{E}\psi) = T[\phi, \omega, \chi, \rho] \in D\psi[\delta, \mathrm{intro}_{\ell}^{\mathcal{K}''}(\phi; \omega; \chi)/h]}$$