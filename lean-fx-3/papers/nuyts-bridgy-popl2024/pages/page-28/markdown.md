8:28

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

Table 1. Classification of related work about parametricity, based on [Nuyts et al. 2017, fig. 9]. Here, $\mathcal{Y}$ is (faintly) highlighted when (possibly) $\mathcal{Y} = \mathcal{X}$; $\mathcal{P}$ is highlighted if $\mathcal{P} = \mathcal{Y} = \mathcal{X}$; and $\mathcal{S}$ is highlighted if $\mathcal{S} = \mathcal{X}$.

|  Citation | Obj. lang. $\mathcal{X}$ | Target lang. $\mathcal{Y}$ | $\mathcal{P}$ | $\mathcal{S}$ | $\mathcal{M}$ | model in $\mathcal{Y}$ or (italic) $\mathcal{M}$  |
| --- | --- | --- | --- | --- | --- | --- |
|  [Reynolds 1983] | System F | Meta: Set theory | $\mathcal{Y}$ | $\mathcal{Y}$ |  | Sets with relations  |
|  [Abadi et al. 1993] | System F | System $\mathcal{R}$ | Meta | Meta | Meta | PERs [Bellucci et al. 1995]  |
|  [Plotkin and Abadi 1993] | System F | System F + logic | Meta | Meta |  |   |
|  [Wadler 2007] | System F | System F + logic | Meta | Meta |  |   |
|  [Atkey 2012] | System F$\omega$ | Meta: Impred. CIC | $\mathcal{Y}$ | $\mathcal{Y}$ |  | Reflexive graphs  |
|  [Takeuti 2001] | $\mathcal{X} \in \lambda$-cube | $\mathcal{X} + \mathcal{V} + \Pi \in \lambda$-cube | Meta | Meta |  |   |
|  [Bernardy et al. 2012] | Any PTS | Suitable PTS | Meta | Meta |  |   |
|  [Tabareau et al. 2021] | CIC | Univalent CIC | Meta | Meta |  |   |
|  [Krishnaswami and Dreyer 2013] | CC | Meta | Meta | Meta |  | PERs  |
|  [Atkey et al. 2014] | MLTT | Meta: CIC | $\mathcal{Y}$ | $\mathcal{Y}$ |  | Reflexive graphs  |
|  [Bernardy and Moulin 2012] | BM | $\mathcal{X}$ | $\mathcal{X}$ | $\mathcal{X}$ |  | none  |
|  [Bernardy et al. 2015] | BCM | $\mathcal{X}$ | $\mathcal{X}$ | Meta | Meta | Affine cubical sets  |
|  [Nuyts et al. 2017] | ParamDTT | $\mathcal{X}$ | $\mathcal{X}$ | Meta | Meta | Bridge/path cubical sets  |
|  [Nuyts and Devriese 2018] | RelDTT | $\mathcal{X}$ | $\mathcal{X}$ | Meta | Meta | Depth n cubical sets  |
|  [Cavallo and Harper 2021] | CH | $\mathcal{X}$ | $\mathcal{X}$ | Meta | Meta | Affine/cart. bicub. sets  |
|  Agda --bridges (Ab) | Ab | $\mathcal{X}$ | $\mathcal{X}$ | Meta | Meta | Affine/CCHM bicub. sets  |
|  ROTT | DTT ($\sim$ Ab) | Ab | $\mathcal{Y}$ | $\mathcal{Y}$ |  | RRGs  |
|  Corollary 4.1 | Pr. Sys. F | Ab | $\mathcal{Y}$ | $\mathcal{Y}$ |  | RRGs  |
|  [Altenkirch et al. 2024] | ACKS | $\mathcal{X}$ | $\mathcal{X}$ | $\mathcal{X}$ | Meta | Affine cubical sets  |
|  Cub. ROTT (envisioned) | $\approx$ ACKS | $\mathcal{X}$ | $\mathcal{X}$ | $\mathcal{X}$ | Ab | Relativistic cubical sets  |

The fourth block lists treatments of internal parametricity for dependent types; these produce concrete free theorems (i.e. not mentioning bridge types that need to be characterized separately) for abstract programs of concrete types. Bernardy and Moulin's [2012] system predates the usage of named relational dimensions, but it is observational, i.e. the SRP holds definitionally. We are unaware of any soundness proof for this system. Bernardy et al. introduce the bridge interval as well as the extent and Gel combinators, and Cavallo and Harper combine their system with HoTT and demonstrate its power on paper. With Agda --bridges, we provide an implementation. The work on ParamDTT and RelDTT introduces a modal system in order to prove Reynolds's identity extension lemma for large types, but in the process has to adopt a cartesian cubical model which does not validate extent. As a consequence, these systems lack the power to prove parametricity of System F, which we demonstrated can be done in Agda --bridges (Section 4.3). We refer to Nuyts [2021] for a brief discussion of various internal parametricity features and their requirements in the model.

Strictly speaking, ROTT is again a dependently typed system with external parametricity that could go in the third block. However, ROTT was conceived as a commodity for Agda --bridges and seeks to obtain free theorems there. This is in contrast with e.g. Atkey et al. [2014], where MLTT is the system of interest but free theorems are obtained in some metatheory. We remark that since param is an external rule, the source syntax of ROTT is really just dependent type theory (extensible with bridge types, which are also displayed RRGs).

The reason why ROTT cannot provide internal parametricity is that the logical relation specified for an RRG, is itself not a displayed RRG (i.e. a dependent ROTT type) but only an external Agda --bridges type. This might be remedied in the future by moving from RRGs to relativistic cubical types, i.e. cubical types whose $n$-cubes are equivalent to $n$-cubes of bridges. Such a system would allow internal parametricity and satisfy the SRP definitionally. The syntax of such a system would

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.