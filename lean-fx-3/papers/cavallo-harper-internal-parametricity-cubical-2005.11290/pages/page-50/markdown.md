5:50

E. CAVALLO AND R. HARPER

Vol. 17:4

We may show that the model interprets Bridge-types—that is, that Bridge-pretypes can be equipped with Kan operations—following the computational definition of coe and hcom in Figure 8; we leave this to the reader. Alternatively, one may follow the definition of composition for Path-types in the BCH model [BCH13, §7.2].

**Theorem 6.13.** $[\square_{ca}^{\mathrm{op}}, \mathbf{Set}]$ *interprets Gel-pretypes*.

*Proof.* We prove the formation rule, following the computational definition in Section 4.4. It is straightforward to see how the introduction and elimination rules follow.

Let a interval term $\boldsymbol{r}: \mathfrak{L}\Psi \to \mathfrak{L}(\boldsymbol{x} : \mathbf{I})$, semantic pretypes $T_0, T_1$ in context $Res!(\mathfrak{L}\Psi, \boldsymbol{r}) \cong \mathfrak{L}(\Psi \backslash \boldsymbol{r})$, and a semantic pretype $R$ in context $\mathfrak{L}(\Psi \backslash \boldsymbol{r}).(T_0 \times T_1)$—here $-.-$ is the semantic equivalent of context extension—be given. We define the Gel-pretype as follows.

$$Gel_{\boldsymbol{r}}(T_0, T_1, R)(\Psi', \psi) := T_{\varepsilon}(\Psi', \psi \backslash \boldsymbol{r}) \quad \text{if } \boldsymbol{r}\psi = \varepsilon$$

$$Gel_{\boldsymbol{r}}(T_0, T_1, R)(\Psi', \psi) := \left\{ (a_0, a_1, t) \left| \begin{array}{l} a_{\varepsilon} \in T_{\varepsilon}(\Psi' \backslash \boldsymbol{r}\psi, \psi \backslash \boldsymbol{r}) \\ t \in (\mathfrak{L}(\psi \backslash \boldsymbol{r}).(a_0 \times a_1))^* R(\Psi' \backslash \boldsymbol{r}\psi, \mathrm{id}) \end{array} \right. \right\} \quad \text{otherwise}$$

As with Bridge-types, the Kan operations may be implemented following the computational definition given in Figure 8. We note that homogeneous composition relies on the closure of the decidable subobject classifier $\Omega_{dec}$ under $\forall \boldsymbol{x}.-$; this parallels the use of $\forall x.-$ for composition in G-, Glue-, or V-types in [BCH13, CCHM15, ABC$^+$19]. As Bridge-types resemble BCH Path-types, so do Gel-types resemble BCH G-types. Coercion for Gel is, however, much simpler than for its cubical equivalents, because the “direction” of a coercion is always a path variable and therefore orthogonal to the direction $\boldsymbol{r}$ of $\mathrm{Gel}_{\boldsymbol{r}}(A, B, R)$: one may coerce “across” a V-type, but not across a Gel-type.

We finish by sketching the interpretation of extent. Suppose we are given dimension term $\boldsymbol{r}: \mathfrak{L}\Psi \to \mathfrak{L}(\boldsymbol{x} : \mathbf{I})$, type $T$ in context $\mathfrak{L}(\Psi \backslash \boldsymbol{r}, \boldsymbol{x} : \mathbf{I})$, and element $t$ of $\mathfrak{L}(\boldsymbol{r}/\boldsymbol{x})^* T$, together with clause data for the endpoint and variable cases. For any $\Psi'$ and $\Psi' \Vdash \psi \in \Psi$, we have $t(\Psi', \psi) \in T(\Psi', (\psi, \boldsymbol{r}\psi/\boldsymbol{x}))$; we proceed by inspecting the status of $\boldsymbol{r}\psi$. If $\boldsymbol{r}\psi$ is an endpoint, then we have $t(\Psi', \psi) \in T(\Psi', (\psi, \boldsymbol{r}\psi/\boldsymbol{x})) = (\mathfrak{L}(\varepsilon/\boldsymbol{x})^* T)(\Psi', \psi)$ and may pass this term to the appropriate endpoint clause. If $\boldsymbol{r}\psi$ is a variable, then we employ the substitution $\Psi' \backslash \boldsymbol{r}\psi, \boldsymbol{y} : \mathbf{I} \Vdash \rho \in \Psi'$ that renames $\boldsymbol{r}\psi$ to a fresh variable $\boldsymbol{y}$. We have $T(\rho)(t(\Psi', \psi)) \in T((\Psi' \backslash \boldsymbol{r}\psi, \boldsymbol{y} : \mathbf{I}), (\psi \backslash \boldsymbol{r}, \boldsymbol{y}/\boldsymbol{x}))$, which per the proof of Theorem 6.12 is exactly a bridge at $T$. We may then supply this bridge to the variable clause of extent.

## 7. RELATED AND FUTURE WORK

**7.1. Related work.** Mechanically, our parametric cubical type theory is not much more than the union of Angiuli *et al.*’s cartesian cubical type theory [AFH18, ABC$^+$19, Ang19] and Bernardy, Coquand, and Moulin’s parametric type theory [BCM15]. As mentioned in Sections 2.4 and 6, we do drop some equations required for Gel-types in the BCM type theory which are not necessary in the cubical setting and complicate model constructions. Accordingly, our proof of relativity is novel. The formulation of context restriction in formalism is also novel, though inspired by Cheney’s work on nominal type theory [Che12], and resolves the issue with admissibility of substitution present in the BCM theory. Finally, Bernardy *et al.* present unary rather than binary parametricity, but from a conceptual perspective this is only a cosmetic difference, a matter of how many constants are included in