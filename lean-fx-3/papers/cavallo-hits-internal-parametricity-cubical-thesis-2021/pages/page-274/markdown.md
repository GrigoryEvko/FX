262

Cohesive parametric type theory

Coercion is more involved, as it analyzes the value of its input. In particular, because we have included formal composites as values of the discrete type, the coercion operator at the discrete type must also handle these elements. Fortunately, this is straightforwardly resolved: a coercion applied to a formal composite reduces to a formal composite of coercions. (This is the same as the reduction used for higher inductive types in Part II.)

Lemma 14.4.11 (Coercion). $\Psi \Vdash \operatorname{Disc}(A) = \operatorname{Disc}(A')$ pretype @ par support coercion for any $\Psi.\mathrm{cc} \gg A = A'$ type @ pt.

Proof. We define a value $\Psi$-PER $Coe^{-1}$ by declaring that $V \approx V' \in Coe^{-1}\langle\psi\rangle$ holds for $\Psi' \Vdash \psi \in \Psi$ exactly when $\Psi' \Vdash V = V' \in \operatorname{Disc}(A)$ and the following are satisfied for all $\Psi', x: \mathbb{I} \Vdash \psi_x \in \Psi$ and $\Psi' \Vdash r, s \in \mathbb{I}$ such that $\psi_x[r/x] = \psi$.

- $\Psi' \Vdash \operatorname{coe}_{x.\operatorname{Disc}(A)\psi_x}^{r \to s}(V) = \operatorname{coe}_{x.\operatorname{Disc}(A')\psi_x}^{r \to s}(V') \in \operatorname{Disc}(A)\psi_x[s/x]$ @ par.
- $\Psi' \Vdash \operatorname{coe}_{x.\operatorname{Disc}(A)\psi_x}^{r \to r}(V) = V \in \operatorname{Disc}(A)\psi$ @ par.

Note that for any terms $N \approx N' \in \Downarrow Coe^{-1}\psi$ and $\psi_x, r, s$ as above, we can deduce that $\Psi' \Vdash \operatorname{coe}_{x.\operatorname{Disc}(A)\psi_x}^{r \to s}(N) = \operatorname{coe}_{x.\operatorname{Disc}(A')\psi_x}^{r \to s}(N') \in \operatorname{Disc}(A)\psi_x[s/x]$ @ par and $\Psi' \Vdash \operatorname{coe}_{x.\operatorname{Disc}(A)\psi_x}^{r \to r}(N) = N \in \operatorname{Disc}(A)\psi$ @ par. This follows by Lemma 3.1.38, as coercion at the discrete type is an eager operator.

We aim to show that $[\![\operatorname{Disc}(A)]\!] \subseteq Coe^{-1}$. By definition of the former as a least fixed-point, it suffices to show that $Mod_{cc}([[A]]) \cup Fhcom(Coe^{-1}) \subseteq Coe^{-1}$, which is to say that $Mod_{cc}([[A]]) \subseteq Coe^{-1}$ and $Fhcom(Coe^{-1}) \subseteq Coe^{-1}$.

Given values $\operatorname{mod}(M) \approx \operatorname{mod}(M') \in Mod_{cc}([[A]])\psi$ and $\psi_x, r, s$ as above, we have by head expansion and coercion in $A$ that $\operatorname{coe}_{x.\operatorname{Disc}(A)\psi_x}^{r \to s}(\operatorname{mod}(M)) = \operatorname{mod}(\operatorname{coe}_{x.A\psi_x}^{r \to s}(M)) \in \operatorname{Disc}(A)\psi_x[s/x]$, likewise for $M'$. It follows that $Mod_{cc}([[A]]) \subseteq Coe^{-1}$.

As for $Fhcom(Coe^{-1}) \subseteq Coe^{-1}$, suppose we are given a pair of values in the former relation, $\operatorname{fhcom}^{t \to u}(M; \overline{\xi_i \hookrightarrow y.N_i}) \approx \operatorname{fhcom}^{t \to u}(M'; \overline{\xi_i \hookrightarrow y.N_i'}) \in Fhcom(Coe^{-1})\langle\psi\rangle$, and $\psi_x, r, s$, as above. By definition of $Fhcom$ and the properties of terms in $Coe^{-1}$, the argument terms $M, M', N_i, N_i'$ may be coerced to obtain well-typed elements of $\operatorname{Disc}(A')\psi_x[s/x]$, then assembled into well-typed formal composites by Rule 14.4.9. That is, the following are well-typed and moreover equal in $\operatorname{Disc}(A)\psi_x[s/x]$.

$$\begin{array}{l} \operatorname{fhcom}^{t \to u}(\operatorname{coe}_{x.\operatorname{Disc}(A)\psi_x}^{r \to s}(M); \overline{\xi_i \hookrightarrow y.\operatorname{coe}_{x.\operatorname{Disc}(A)\psi_x}^{r \to s}(N_i)}) \in \operatorname{Disc}(A)\psi_x[s/x] \text{ @ par} \\ \operatorname{fhcom}^{t \to u}(\operatorname{coe}_{x.\operatorname{Disc}(A')\psi_x}^{r \to s}(M'); \overline{\xi_i \hookrightarrow y.\operatorname{coe}_{x.\operatorname{Disc}(A')\psi_x}^{r \to s}(N_i')}) \in \operatorname{Disc}(A)\psi_x[s/x] \text{ @ par} \end{array}$$

It now follows by the definition of the operational semantics and coherent head expansion that the term $\operatorname{coe}_{x.\operatorname{Disc}(A)\psi_x}^{r \to s}(\operatorname{fhcom}^{t \to u}(M; \overline{\xi_i \hookrightarrow y.N_i}))$ is equal to the former, likewise