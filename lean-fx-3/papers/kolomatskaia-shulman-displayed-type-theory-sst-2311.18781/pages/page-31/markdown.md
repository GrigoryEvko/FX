and that its computation rules should be:

$$Z \left( R_T \bar{Z} \bar{S} \sigma \right) \equiv \bar{Z} \sigma$$

$$S \left( R_T \bar{Z} \bar{S} \sigma \right) a_3 \equiv \left( R_T \bar{Z} \bar{S} \right)^d \langle \sigma, \bar{S} \sigma a_3 \rangle.$$

Now, the expression $\left( R_T \bar{Z} \bar{S} \right)^d$ defines a meta abstracted-term of meta-abstracted type $\left( \left( SST_f^d \left( R_T \bar{Z} \bar{S} v^{+ev} \right) \right) \right)_{v^+, \gamma^0}$. One reasonable hope is that the display in the above line could be computed in terms of a corecursor for $SST_f^d$. However, this approach runs into issues. Towards this aim, let us more generally try to work out the coinduction principle that would let us define $f : (x : X) \to SST_f^d (A x)$ for $\Gamma$, $\widehat{\mathbf{A}}_{\triangle \square} \vdash_{sm} A : X \to SST_f^d$. We apply the same methodology as before, and start by writing down reasonable looking code:

$$\begin{array}{l} f : (t : X) \to SST^d (A t) \\ Z^d (f t) a = (?_{Z_2} : \text{Type}) \\ S^d (f t) a b = f^d t (?_{S_3} : X^d t) \end{array}$$

However, we then have:

$$\begin{array}{l} \Gamma, \widehat{\mathbf{A}}_{\triangle \square}, t : X, a : \text{EI} (Z (A t)), b : \text{EI} ?_{Z_2} \vdash_{sm} S^d (f t) a b : SST_f^{dd} (A t) (f t) (S (A t) a) \\ \Gamma, \widehat{\mathbf{A}}_{\triangle \square}, t : X, a : \text{EI} (Z (A t)), b : \text{EI} ?_{Z_2} \vdash_{sm} f^d t ?_{S_3} : SST_f^{dd} (A t) (A^d t ?_{S_3}) (f t) \end{array}$$

We see then that there is an index ordering mismatch that seems to prevent us from writing down a coinduction principle for $SST_f^d$ corresponding to a simple class of syntactic tricks as above. If dTT were extended to have symmetries, then we could make progress here by lining up the $f$ $t$ indices and imposing the definitional equality $S (A t) a \equiv A^d t ?_{S_3}$ as a corecursor premise. On the other hand, without the ability to line up the two $f$ $t$ indices, trying to instead impose definitional equalities involving $f$, the very term being defined, creates a vicious cycle, since whether or not a definition of $f$ is well-typed would depend on checking a definitional equality with $f$, which presupposes that $f$ is well-typed. Since, for the present, we have chosen to develop a theory without symmetries, we must abandon this approach.

To salvage this, we will leave $(R_T \bar{Z} \bar{S})^d$ as a stuck form in the theory, but will specify how to compute $Z^d$ and $S^d$ on this normal form. The main idea is that if we define:

$$\begin{array}{l} f : X \to SST \\ Z (f t) = j t \\ S (f t) a = f^d t (s t a) \end{array}$$

then we can compute display on each line of this definition to obtain:

$$\begin{array}{l} f^d : (t : X) \to X^d t \to SST^d (f t) \\ Z^d (f^d t s) = \lambda a \to j^d t s a \\ S^d (f^d t s) a_i a_i = f^{dd} t s (s t a_i) (s^d t s a_i a_i) \end{array}$$

Thus we obtain the computation laws:

$$\begin{array}{l} Z^d \left( (R_T \bar{Z} \bar{S})^d \sigma^+ \right) a \equiv \bar{Z}^d \sigma^+ a \\ S^d \left( (R_T \bar{Z} \bar{S})^d \sigma^+ \right) a_i a_i \equiv (R_T \bar{Z} \bar{S})^{dd} \langle \sigma^+, \bar{S}^D \sigma^+ a_i a_i \rangle \end{array}$$

31