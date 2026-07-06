3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

### 3.2.4 Complicial thinness extensions

Notation. In this section, we will often consider morphisms $\tilde{a} \to \tilde{b}$ that fit into cocartesian squares:

$$\begin{array}{c} a \xrightarrow {i} b \\ \Big \downarrow \quad \Big \downarrow \\ \tilde {a} \longrightarrow \tilde {b} \end{array}$$

where $a \to \tilde{a}$ and $b \to \tilde{b}$ are epimorphisms. To avoid complicating the notations unnecessarily, the induced morphism $\tilde{a} \to \tilde{b}$ will just be denoted $i$.

Lemma 3.2.4.1. Morphisms $([n]^{0})' \to ([n]^{0})''$ and $([n]^{n})' \to ([n]^{n})''$ are acyclic cofibrations.

Proof. For $k$ equal to 0 or $n$, we have pushout diagrams:

$$\begin{array}{c} [ n ] ^ {k} \longrightarrow ([ n ] ^ {k}) ^ {\prime} \longrightarrow ([ n ] ^ {k}) ^ {\prime \prime} \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ n - 1 ] \longrightarrow [ n - 1 ] _ {t} \xrightarrow [ i d ]{} [ n - 1 ] _ {t} \end{array}$$

Propositions 3.2.2.5 and 3.2.3.16 imply that both $s^0 : [n]^0 \to [n-1]$ and $s^{n-1} : [n]^{n-1} \to [n-1]$ are weak equivalences. As horizontal morphisms are cofibrations, the left properness imply that all the vertical morphisms are weak equivalences. By two out of three, this shows that $([n]^k)' \to ([n]^k)''$ is a weak equivalence.

Construction 3.2.4.2. The propositions 3.2.1.6 and 3.2.1.8 provide canonical morphisms:

$$\begin{array}{l} \alpha_ {a}: [ e \star a, 1 ] \rightarrow e \star [ a, 1 ] \quad \beta_ {a}: [ e, 1 ] \vee [ a, 1 ] \rightarrow e \star [ a, 1 ] \\ \delta_ {a}: [ e \star a, 1 ] \vee [ a, 1 ] \rightarrow e \star [ a, 2 ] \quad \epsilon_ {a}: [ [ 2 ] \bar {\otimes} a, 1 ] \rightarrow e \star [ a, 2 ] \end{array}$$

where $[2] \bar{\otimes} a$ and $[e \star a, 1] \vee [a, 1]$ are the following pushouts:

$$\begin{array}{c} [ 1 ] \otimes a \amalg [ 1 ] \otimes a \xrightarrow {d ^ {1} \otimes a \amalg d ^ {2} \otimes a} [ 2 ] \otimes a \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star a \amalg e \star a \xrightarrow [ d ^ {1} \bar {\otimes} a \amalg d ^ {2} \bar {\otimes} a ]{} [ 2 ] \bar {\otimes} a \end{array}$$

$$\begin{array}{c} [ [ 1 ] \otimes a, 1 ] \amalg [ [ 1 ] \otimes a, 1 ] ^ {[ [ 1 ] \otimes a, d ^ {2} \amalg d ^ {0} ]} [ [ 1 ] \otimes a, 2 ] \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e \star a, 1 ] \amalg [ a, 1 ] \longrightarrow [ e \star a, 1 ] \vee [ a, 1 ] \end{array}$$

Moreover they fit in the following commutative diagram:

$$\begin{array}{l} [ a, 1 ] \xrightarrow [ d ^ {0} \star [ a , 1 ] ]{\left[ a , d ^ {0} \right]} [ e, 1 ] \vee [ a, 1 ] \\ \Biggl \downarrow \beta_ {a} \\ e \star [ a, 1 ] \end{array}$$

$$\begin{array}{c} [ a, 1 ] \xrightarrow {\left[ d ^ {0} \star a , 1 \right]} [ e \star a, 1 ] \\ [ a, d ^ {1} ] \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e, 1 ] \vee [ a, 1 ] \xrightarrow {\beta_ {a}} e \star [ a, 1 ] \end{array} \tag {2}$$

$$\begin{array}{l} [ e \star a, 1 ] \xrightarrow [ e \star [ a , d ^ {2} ] ]{\left[ e \star a, 1 \right]} [ e \star a, 1 ] \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {2} ] ]{\alpha_ {a}} e \star [ a, 2 ] \end{array} \tag {3}$$

$$\begin{array}{c} [ e \star a, 1 ] \xrightarrow [ e \star [ a , d ^ {1} ] ]{\left[ d ^ {1} \bar {\otimes} a, 1 \right]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ \alpha_ {a} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {1} ] ]{\epsilon_ {a}} e \star [ a, 2 ] \end{array} \tag {4}$$

$$\begin{array}{l} [ [ 1 ] \otimes a, 1 ] \xrightarrow [ d ^ {0} \otimes a, 1 ]{\left[ d ^ {0} \otimes a, 1 \right]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ [ [ 1 ] \otimes a, d ^ {1} ] \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [ e \star a, 1 ] \vee [ a, 1 ] \xrightarrow [ \delta_ {a} ]{} e \star [ a, 2 ] \end{array} \tag {5}$$

$$\begin{array}{c} [ e \star a, 1 ] \xrightarrow [ d ^ {2} \bar {\otimes} a, 1 ]{\left[ d ^ {2} \bar {\otimes} a, 1 \right]} [ [ 2 ] \bar {\otimes} a, 1 ] \\ \alpha_ {a} \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star [ a, 1 ] \xrightarrow [ e \star [ a , d ^ {0} ] ]{} e \star [ a, 2 ] \end{array} \tag {6}$$

125