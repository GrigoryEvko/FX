40

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

By (U1) we conclude that $\pi_{\mathcal{U}_i}$ lies in $\mathcal{V}_i$, and it is moreover a Kan fibration almost by definition. Fix a commutative diagram of the following shape:

$$\begin{array}{ccc} \Lambda_i^n & \longrightarrow & E_{\mathcal{U}_i} \\ \updownarrow & & \updownarrow \\ \Delta^n & \xrightarrow[\alpha]{} & U_{\mathcal{U}_i} \end{array}$$

By definition of $\pi_{\mathcal{U}_i}$, pulling back along $\alpha$ yields a Kan fibration, whereby we obtain the necessary lift:

$$\begin{array}{ccc} \Lambda_i^n & \dashrightarrow & E_{\mathcal{U}_i} \\ \updownarrow & & \updownarrow \\ \Delta^n & \xrightarrow{\quad} & \Delta^n \end{array} \xrightarrow{\quad} \begin{array}{c} E_{\mathcal{U}_i} \\ \updownarrow \\ \downarrow \\ U_{\mathcal{U}_i} \end{array}$$

Consequently, $\pi_{\mathcal{U}_i} \in \mathcal{U}_i$. It remains to show that $\pi_{\mathcal{U}_i}$ satisfies (U8). Accordingly, fix a pair of cartesian squares $\alpha: f \longrightarrow \pi_{\mathcal{U}_i}$ and $i: f \longmapsto g$. We apply (U8) for $\mathcal{V}_i$ to obtain a cartesian square $\beta: g \longrightarrow \pi_{\mathcal{V}_i}$ fitting into the following commutative diagram:

$$\begin{array}{ccc} f & \xrightarrow{\alpha} & \pi_{\mathcal{U}_0} \longmapsto \pi_{\mathcal{V}_0} \\ \updownarrow & & \updownarrow \\ g & & \beta \end{array}$$

To complete the proof, it suffices to show that $\beta$ factors through $\pi_{\mathcal{U}_i}$ i.e. that for any cartesian square $h \longrightarrow g$ such that $h$ has a representable base, $h$ is a Kan fibration. This, however, follows immediately because $g$ is a Kan fibration. ■

We recall a purely homotopy-theoretic fact, referred to by Awodey [Awo21] as the fibration extension property.

6.2.2. LEMMA. Given a Kan fibration $f: X \longrightarrow A$ and a trivial cofibration $i: A \longmapsto B$, there is a Kan fibration $g: Y \longrightarrow B$ such that $i^*g = f$. Additionally, if $f \in \mathcal{V}_i$ then $g \in \mathcal{V}_i$.

This result is proved by Kapulkin, Lumsdaine, and Voevodsky [KL21] using Quillen's theory of minimal fibrations. An alternative approach is given by Lurie [Lur22, Tag 00ZS] using Kan's $\mathsf{Ex}_\infty$ functor. A near immediate consequence of Lemma 6.2.2 and (U8) is the fibrancy of the $U_{\mathcal{U}_0}$:

6.2.3. THEOREM. The object $U_{\mathcal{U}_0}$ lies within $\mathcal{U}_1$.