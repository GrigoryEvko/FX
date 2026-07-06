STRICT UNIVERSES FOR GROTHENDIECK TOPOI

41

PROOF. As a subobject of $\mathcal{V}_0$, (U2) implies that $U_{\mathcal{U}_0}$ lies within $\mathcal{V}_1$, so it suffices to show that $U_{\mathcal{U}_0}$ is a Kan complex. Accordingly, we fix a lifting problem for $U_{\mathcal{U}_0}$:

$$\begin{array}{c} \Lambda_i^n \xrightarrow{\alpha} U_{\mathcal{U}_0} \\ \Big\downarrow \\ \Delta^n \end{array}$$

We must extend $\alpha$ along the inclusion $\Lambda_i^n \to \Delta^n$. We begin by pulling back $\pi_{\mathcal{U}_0}$ along $\alpha$, obtaining a Kan fibration $[\alpha] \to \Lambda_i^n$ and a cartesian map $h: [\alpha] \to \pi_{\mathcal{U}_0}$. Applying Lemma 6.2.2, we can extend $[\alpha]$ along $\Lambda_i^n \to \Delta^n$ to another Kan fibration $[\beta] \to \Delta^n$. Next, we apply (U8) to extend $h$ along the induced cartesian monomorphism $[\alpha] \to [\beta]$:

$$\begin{array}{c} [\alpha] \xrightarrow{h} \pi_{\mathcal{U}_0} \\ \Big\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{[}\beta\text{]} \end{array}$$

The downstairs component of $\beta: [\beta] \to \pi_{\mathcal{U}_0}$ then solves the original lifting problem. ■

Notice that in the above proof, the application of (U8) allows us to rephrase a property of the generic family (“$U_{\mathcal{U}_0}$ is a Kan complex”) as a property of the class of maps $\mathcal{U}_0$ (“Kan fibrations extend along trivial cofibrations”) to which the standard tools of homotopy theory apply. While the setup is more complex, the same is true of the proof that $\pi_{\mathcal{U}_0}$ is univalent. Prior to discussing the proof of univalence, we must fix a few definitions.

6.2.4. DEFINITION. Given Kan fibrations $E_0, E_1 \to B$, we define $\mathsf{Equiv}(E_0, E_1) \to B$ to be the fibration of weak equivalences between $E_0$ and $E_1$, i.e. the subobject of the local exponential $E_1^{E_0} \to B$ spanned by weak equivalences.

Explicitly, a simplex $\alpha: \Delta^n \to E_1^{E_0}$ factors through $\mathsf{Equiv}(E_0, E_1)$ if the corresponding morphism $\alpha^* E_0 \to \alpha^* E_1$ over $\Delta^n$ is a weak equivalence. In fact, a map $X \to \mathsf{Equiv}(E_0, E_1)$ is determined by a pair of maps $f_i: X \to B$ along with a weak equivalence $f_0^* E_0 \to f_1^* E_1$ over $X$.

We have avoided a number of subtle points in this definition e.g., that weak equivalences between fibrations are stable under pullback to show that it is well-defined. These are addressed thoroughly by Kapulkin, Lumsdaine, and Voevodsky [KL21]. See Shulman [Shu15] for a less analytic definition of the object of equivalences.

Given a Kan fibration $X \to B$, we define $\langle \partial_0, \partial_1 \rangle: \mathsf{Eq}(X) \to B \times B$ to be $\mathsf{Equiv}(\pi_1^* X, \pi_2^* X)$, i.e. the object of equivalences between two specified fibers of $X$. We observe that there is a canonical monomorphism $\delta_X: B \mapsto \mathsf{Eq}(X)$ lying over the diagonal map $B \mapsto B \times B$