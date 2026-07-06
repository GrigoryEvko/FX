44

Martin-Löf's type theory

This property is indeed satisfied by ITT, reflecting intuitively that it includes the necessary rules for calculating the results of eliminators and substitutions at each type. Adequacy expresses a kind of constructive character of a formalism: for example, if we construct a term of natural number type, it can be “run” to obtain an explicit natural number. Note that a formalism that is constructive in this sense may still have non-constructive models: adequacy only shows that elements definable in the formalism can be computed.

### 2.2.2 A non-computational model

As mentioned above, properties like adequacy of a formalism do not prevent us from interpreting that formalism in non-constructive settings. As an example, we sketch a set-theoretic interpretation of the formalism described above.

We begin by interpreting contexts $\Gamma$ as sets $[\![\Gamma]\!] \in Set$ and substitutions $\Gamma' \vdash \gamma : \Gamma$ as set-theoretic functions, $[\![\gamma]\!] : [\![\Gamma']\!] \to [\![\Gamma]\!]$. We interpret $\Gamma \vdash A$ type as a family of sets $([\![A]\!]_I)_{I \in [\![\Gamma]\!]}$, and terms $\Gamma \vdash M : A$ as families of elements: $([\![M]\!]_I)_{I \in [\![\Gamma]\!]}$ where $[\![M]\!]_I \in [\![A]\!]_I$ for each $I \in [\![\Gamma]\!]$. The equality judgments are interpreted by set-theoretic equality. Application of substitution is interpreted by reindexing of families: given $\Gamma' \vdash \gamma : \Gamma$ and $\Gamma \vdash A$ type, we define $[\![A[\gamma]]\!]_I := [\![A]\!]_{\gamma}$. We interpret the empty context by a one-element set, $[\![\cdot]\!] := \{\star\}$, and context extension by disjoint union (i.e., coproduct) over the elements of the base context: $[\![\Gamma.A]\!] := \coprod_{I \in [\![\Gamma]\!]} [\![A]\!]_I$.

Moving on to type formers, we can interpret dependent function types as products, $[\![A \to B]\!]_I := \prod_{a \in [\![A]\!]_I} [\![B]\!]_{(I,a)}$, and dependent products as disjoint unions $[\![A \times B]\!]_I := \coprod_{a \in [\![A]\!]_I} [\![B]\!]_{(I,a)}$. The identity type $\text{Id}(A, M_0, M_1)$ can be interpreted as a one-element set when $M_0$ and $M_1$ are equal and the empty set otherwise.

$$[\text{Id}(A, M_0, M_1)]_I := \{\star \mid [\![M_0]\!]_I = [\![M_1]\!]_I\}$$

We may interpret the universe by assuming that our set theory supports a Grothendieck universe, essentially a set large enough to be closed under the various type formers.