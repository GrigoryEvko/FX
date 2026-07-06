32

E. Cavallo and C. Sattler

### 4.2.3 Universe

To define a universe classifying fibrations, we use a theorem of Licata, Orton, Pitts, and Spitters [LOPS18]. The cardinal $\kappa$ provides a Grothendieck universe in Set, from which Hofmann and Streicher's construction produces a universe $p_U \colon \widetilde{U} \to U$ in $\mathrm{PSh}(\square_\nu)$ classifying $\kappa$-small maps [HS97; Str05; Awo24]. Our classifier for $\kappa$-small fibrations shall be a subuniverse of $p_U$. The key property of $\mathrm{PSh}(\square_\nu)$ is that the cocylinder $(-)^\mathbb{I}$ has a right adjoint, i.e., that $\mathbb{I}$ is internally tiny: we have $(-)^\mathbb{I} \cong ((-) \times [1])^*$ and therefore $(-)^\mathbb{I} \dashv \sqrt{-} := ((-) \times [1])_+$. This property is common to cube categories but fails for example in simplicial sets. We refer to Swan [Swa22] for a deeper analysis.

Given a $\kappa$-small map $f \colon Y \to X$ with characteristic map $A \colon X \to U$, we define a family $X^\mathbb{I} \to U$ whose sections correspond to fibration structures on $A$. To do so, it is convenient to work in the internal extensional type theory of the universe $p_U$ in the style of Orton and Pitts [OP18].$^5$ Writing $\top \colon 1 \to \Omega$ for the subobject classifier in $\mathrm{PSh}(\square_\nu)$, the maps $!_\Omega \colon \Omega \to 1$ and $\top$ are both classified by $p_U$,$^6$ so appear as a closed type $\cdot \vdash \Omega : U$ and type family $\varphi \colon \Omega \vdash [\varphi] : U$ respectively. The interval likewise appears as a closed type $\cdot \vdash \mathbb{I} : U$ with inhabitants $\cdot \vdash 0, 1 : \mathbb{I}$.

Definition 4.26 Given a type $A \colon U$, define its type of trivial fibration structures $\mathrm{TFib}\, A \colon U$ as follows:

$$\mathrm{TFib}\, A := \Pi \varphi \colon \Omega. \, \Pi \nu \colon [\varphi] \to A. \, \Sigma a \colon A. \, \Pi a \colon [\varphi]. \, \nu(a) = a.$$

Definition 4.27 Given $k \in \{0, 1\}$ and $A \colon X \to U$, define the pullback exponential $(\delta_k \xrightarrow{\sim} A) : (\Sigma p \colon X^\mathbb{I}. A(p(k))) \to U$ internally as follows:

$$(\delta_k \xrightarrow{\sim} A)(p, a) := \Sigma q \colon (\Pi i \colon \mathbb{I}. A(p(i))). \, q(k) = a.$$

Definition 4.28 Given $A \colon X \to U$, define $\mathrm{Fib}_k\, A \colon X^\mathbb{I} \to U$ for $k \in \{0, 1\}$ and then $\mathrm{Fib}\, A \colon X^\mathbb{I} \to U$ as follows:

$$(\mathrm{Fib}_k\, A)(p) := \Pi a \colon A(p(k)). \, \mathrm{TFib}((\delta_k \xrightarrow{\sim} A)(p, a))$$

$$(\mathrm{Fib}\, A)(p) := (\mathrm{Fib}_0\, A)(p) \times (\mathrm{Fib}_1\, A)(p).$$

Proposition 4.29 Let $f \colon Y \to X$ be given with classifying map $A \colon X \to U$. Then $f$ is a uniform fibration if and only if the type $\Pi p \colon X^\mathbb{I}$. $(\mathrm{Fib}\, A)(p)$ is inhabited.

Proof See [AGH24, Corollary 8.7].

Using the right adjoint to $(-)^\mathbb{I}$, we carve out the subuniverse of $p_U$ corresponding to families $A \colon X \to U$ for which $\Pi p \colon X^\mathbb{I}$. $(\mathrm{Fib}\, A)(p)$ is inhabited. For this step we return to working externally, as $\sqrt{-}$ does not straightforwardly internalize; Licata et al. [LOPS18] use a global sections modality to axiomatize $\sqrt{-}$ internally, while Riley [Ril24]

$^5$We refer to [AGH24] for a detailed translation between external and internal constructions in presheaf categories and to [Awo23, §6] for a fully externalized argument.

$^6$If working predicatively, one should replace $\Omega$ with the classifier for levelwise decidable subobjects.

2025/10/16 00:43