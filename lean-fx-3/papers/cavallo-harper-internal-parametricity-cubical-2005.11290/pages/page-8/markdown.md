5:8

E. CAVALLO AND R. HARPER

Vol. 17:4

operations such as transitivity and symmetry of paths. Finally, additional machinery is required to obtain univalence, the correspondence between paths of types and isomorphisms.

We follow Angiuli et al.'s account of cubical type theory [AFH18, ABC$^{+}$19], known as *cartesian cubical type theory*. Other cubical type theories and models [BCH13, CCHM15, Awo18, OP18, CMS20] vary in their treatment of the interval and formulation of the Kan operations. Although we commit to one theory here for simplicity, we expect that this paper can be replayed without difficulty using any other.

To begin at the beginning, cubical type theory is—like Martin-Löf's type theories [ML75, ML82]—based on four judgments: *A is a type, A and B are equal types, M has type A, and M and N are equal elements of type A*, all relative to a context $\Gamma$ of typed variables.

$$\Gamma \gg A \text{ type} \qquad \Gamma \gg A = B \text{ type} \qquad \Gamma \gg M \in A \qquad \Gamma \gg M = N \in A$$

A final judgment $\Gamma \text{ ctx}$ ($\Gamma$ is a context) specifies the well-formed variable contexts, which are lists of assumptions of the form $a : A$ (a ranges over terms of type $A$) among others we will introduce in a moment. (We will follow standard practice in omitting the prefix $\Gamma \gg$ from judgments when the context is irrelevant to the discussion.) Note that the equality judgments express an external, contentless equality, which is distinct from the contentful path equality. The external 'exact' equality is necessary on the judgmental level, but it need not be accessible from within the theory.

It is useful to further introduce a *substitution* judgment $\Gamma' \gg \gamma \in \Gamma$ (with equality counterpart $\Gamma' \gg \gamma = \gamma' \in \Gamma$); a substitution is a list $\gamma = (M_1/a_1, \dots, M_n/a_n)$ instantiating each variable in $\Gamma$ with a term over the variables in $\Gamma'$. We write $N\gamma$ for the application of $\gamma$ to a term $N$, that is, the result of replacing each occurrence of $a_i$ in $N$ with $M_i$. Each of the judgments above is preserved by substitution; for example, if $\Gamma' \gg \gamma \in \Gamma$ and $\Gamma \gg M \in A$, then $\Gamma' \gg M\gamma \in A\gamma$.

We think of these judgments as speaking about programs $A, B, M, N$ in some untyped language with an operational semantics. They are *behavioral specifications*: $\Gamma \gg A$ type means that for any instantiation of the hypotheses $\Gamma$, the program $A$ computes a value that names some specification. Likewise, $\Gamma \gg M \in A$ means that $M$ computes to a value satisfying the specification computed by $A$. We use the notation $\gg$ and $\in$ (as opposed to the typical $\vdash$ and $\cdot$) to indicate that we are speaking about this computational interpretation; we will develop a purely formal counterpart for the theory in Section 5. For the moment, we will be vague about the exact meaning of 'computes' in the cubical setting, in the interest of first giving a sense of the shape of cubical and parametric type theory. We lay out the computational interpretation in detail in Section 4. Until that point, we describe the system by presenting inference rules that will turn out to be true in the semantics; note that these are theorems, not definitions.

1.1. **The interval.** Cubical type theory adds a new form of judgment, $\Gamma \gg r \in \mathbb{I}$ ($r$ is an interval term), and its associated equality judgment $\Gamma \gg r = s \in \mathbb{I}$. The two endpoints are interval terms, and we can add interval variables to the context.

$$\overline{\Gamma \gg 0 \in \mathbb{I}} \qquad \overline{\Gamma \gg 1 \in \mathbb{I}} \qquad \overline{\Gamma \text{ ctx}} \qquad \overline{\Gamma, x : \mathbb{I} \text{ ctx}} \qquad \overline{\Gamma, x : \mathbb{I} \gg x \in \mathbb{I}}$$

Interval variables behave just like term variables, at least in the sense that they are *structural*: we have weakening, contraction, and exchange principles, as embodied by the following