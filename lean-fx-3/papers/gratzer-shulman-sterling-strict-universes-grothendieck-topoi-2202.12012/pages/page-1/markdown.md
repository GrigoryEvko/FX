arXiv:2202.12012v3 [math.CT] 16 May 2024

# STRICT UNIVERSES FOR GROTHENDIECK TOPOI

DANIEL GRATZER AND MICHAEL SHULMAN AND JONATHAN STERLING

ABSTRACT. Hofmann and Streicher famously showed how to lift Grothendieck universes into presheaf topoi, and Streicher has extended their result to the case of sheaf topoi by sheafification. In parallel, van den Berg and Moerdijk have shown in the context of algebraic set theory that similar constructions continue to apply even in weaker metatheories. Unfortunately, sheafification seems not to preserve an important *realignment* property enjoyed by presheaf universes that plays a critical role in models of univalent type theory as well as synthetic Tait computability. When multiple universes are present, realignment also implies a *coherent* interpretation of connectives across all universes that justifies the cumulativity laws present in popular formulations of Martin-Löf type theory.

We observe that a slight adjustment to an argument of Shulman lifts a well-behaved cumulative universe hierarchy in the category of sets to a cumulative universe hierarchy satisfying the realignment property at every level in any Grothendieck topos. Hence one has direct interpretations of Martin-Löf type theory with cumulative universes into all Grothendieck topoi. A further implication is to extend the reach of recent synthetic methods in the semantics of cubical type theory and the syntactic metatheory of type theory and programming languages to all Grothendieck topoi.

# Contents

|  1 | Introduction | 2  |
| --- | --- | --- |
|  1.1 | Elementary axioms for universes in a topos | 3  |
|  1.2 | From realignment to cumulative hierarchies | 6  |
|  1.3 | Structure of the paper | 6  |
|  2 | Reviewing Hofmann and Streicher's universes | 7  |
|  2.1 | Universes of sets | 7  |
|  2.2 | Hofmann and Streicher's universe of presheaves | 8  |
|  2.3 | Streicher's universe of sheaves | 11  |
|  3 | Generalities on descent and $\kappa$-compactness | 13  |
|  3.1 | Descent in a Grothendieck topos | 13  |
|  3.2 | Compact objects and relatively compact maps | 18  |
|  3.3 | Relating small and relatively compact maps | 21  |
|  4 | Main result: a universe satisfying realignment | 25  |
|  4.1 | Saturation of solvable realignment problems | 25  |
|  4.2 | A small object argument | 29  |
|  4.3 | Realignment for the universe | 30  |
|  4.4 | A cumulative universe hierarchy | 32  |

© Daniel Gratzer and Michael Shulman and Jonathan Sterling, 2022–2024. Permission to copy for private use granted.

1