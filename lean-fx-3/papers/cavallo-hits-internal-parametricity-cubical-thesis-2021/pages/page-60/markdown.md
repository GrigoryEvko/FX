48*Cubical type theory*

variations on structural cubical sets. In both cases, the result was not merely a constructive model but a *cubical type theory*. In the CCHM case, this came in the form of a formalism with an interpretation in cubical sets and a canonicity result due to Huber [Hub19]; in the AFH case, in the form of a type theory in our computational sense. Each presented a theory with a full-fledged, infinite hierarchy of univalent universes, along with examples of higher inductive types. Apart from the difference in settings (formal vs. computational), the CCHM and AFH approaches are broadly similar, but do differ substantially in the finer details. In technical terms, CCHM is based on the *De Morgan cube category*, while AFH is based on the *cartesian cube category*; that basic difference leads to divergences in the ways coercions are calculated at each type. The CCHM model is generalized to give a variety of topos models for De Morgan cubical type theory in [OP18; LOPS18]; the same is done for cartesian type theory in [ABCFHL19]. Cavallo, Mörtberg, and Swan show that the two branches can be viewed as instances of a single construction [CMS20]. As in **2DTT**, the basic move in each of these theories is to treat contentful identities as internalizations of a judgmental phenomenon. in the cubical case, that structure is dependency on an interval variable.

**Outline** We begin in Section 3.1 with a framework for cartesian cubical type theories in the style of Angiuli, Favonia, and Harper, hewing most closely to the account presented in Angiuli's dissertation [Ang19]. With an instance of the framework in hand, we exercise it a bit in Section 3.2, proving some elementary results in cubical type theory that will serve us later on. As with Martin-Löf type theory, we round out the chapter with a discussion of formalisms and non-computational models in Section 3.3.

## 3.1 Cubical computational type theory

To start, let us lay out the structure we intend cubical type theories to support. The distinguishing characteristic of all cubical type theories is the ability to assume an interval variable.

$$
\frac{\Gamma \operatorname{ctx}}{(\Gamma, x : \mathbb{I}) \operatorname{ctx}}
$$

Although this notationally resembles an ordinary term hypothesis $a : A$, it is really a separate context forming operation; the interval is not a type. Interval *terms*, which can be substituted for such variables, are characterized by separate judgments $\Gamma \gg r \in \mathbb{I}$ and $\Gamma \gg r = s \in \mathbb{I}$, the resemblance to $\Gamma \gg M \in A$ and $\Gamma \gg M = N \in A$ again being merely suggestive. The intuition is that $\mathbb{I}$ is an interval in the sense of topology, a space with two