44

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

By (U8) we solve the following realignment problem to obtain an extension of the code $\beta: A \longrightarrow U_{\mathcal{U}_0}$ along $A \longmapsto B$, using the fact that $[\bar{\beta}]$ lies in $\mathcal{U}_0$ by assumption:

$$\begin{array}{c} [\beta] \xrightarrow{\beta} \pi_{\mathcal{U}_0} \\ f \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \tag{43}$$

The indicated lift of Diagram 43 then supplies in conjunction with the weak equivalence $\bar{w}: [\bar{\beta}] \longrightarrow [\bar{\alpha}]$ the required lift for Diagram 40:

$$\begin{array}{c} A \xrightarrow{(\beta, \alpha, w)} \mathsf{Eq}(E_{\mathcal{U}_0}) \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \end{array} \begin{array}{c} \downarrow \\ B \xrightarrow{(\bar{\beta}, \bar{\alpha}, \bar{w})} \\ \downarrow \\ \bar{\alpha} \end{array} \begin{array}{c} \downarrow \\ \downarrow \\ U_{\mathcal{U}_0} \end{array} \partial_1$$

Therefore $\partial_1$ is a trivial fibration and thus $\pi_{\mathcal{U}_0}$ is univalent.

6.3. ARTIN GLUING AND SYNTHETIC TAIT COMPUTABILITY. Artin gluing is used by computer scientists to prove metatheorems for type theories and programming languages such as normalization, canonicity, decidability, parametricity, conservativity, and computational adequacy. Sterling and Harper [SH21] have introduced synthetic Tait computability as an abstraction for working in the internal language of glued topoi, taking the realignment law (U8) in its internal form (see Section 5) as a basic axiom.

6.3.1. HISTORY AND MOTIVATION. Synthetic Tait computability (or STC) was first employed in op. cit. to prove a generalized abstraction/parametricity theorem for a language of software packages (“modules”) in the style of Standard ML; subsequently, Sterling and Angiuli [SA21] used STC to positively resolve the long-standing normalization conjecture for cubical type theory [Ang+21].⁴ Building on these results, Gratzer [Gra22] adapted STC to verify the analogous conjecture for multimodal type theory [Gra+20]. In their original formulation, all of these results relied heavily on (U8), but the glued topoi in the cited results were all of presheaf type and hence the presheaf-theoretic universes of Hofmann and Streicher [HS97] could be brought to bear without broaching the question of strict universes in sheaf topoi.

More recently, synthetic Tait computability has been employed in scenarios where the glued topos is not known to be of presheaf type. For example, Gratzer and Birkedal

⁴See also Sterling’s dissertation [Ste21] for a more detailed treatment of both this result and synthetic Tait computability in general.