3.2. COMPLICIAL GRAY MODULE STRUCTURE ON tSeg(A)

Definition 3.2.3.1. A marked Segal A-precategory is a stratified Segal A-precategory having the right lifting property against all entire acyclic cofibrations. We denote by mSeg(A) the full subcategory of marked Segal A-precategory. We then have an adjunction:

$$(\_)_{\mathrm{mk}} : \mathrm{tSeg}(A) \xrightleftharpoons{\perp} \mathrm{mSeg}(A) : \iota$$

where the left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified Segal A-precategory $(C, tC)$ to the marked Segal A-precategory $(C, \overline{tC})$, where $\overline{tC}$ is the smaller stratification that includes $tC$ and makes $(C, \overline{tC})$ a marked Segal A-precategory, and where the right adjoint is a fully faithful inclusion. Remark furthermore that at the level of preshaves, these two adjoints are the identity. We denote by $r_C : C \to C_{\mathrm{mk}}$ the canonical inclusion. The proposition 2.1.2.11 states that $r_C$ is an entire acyclic cofibration.

There is an isomorphism $(e \star C_{\mathrm{mk}})_{\mathrm{mk}} \cong (e \star C)_{\mathrm{mk}}$. Indeed $e \star \_$ preserves both entire cofibrations and weak equivalences, we have two entire acyclic cofibration $e \star C \to (e \star C)_{\mathrm{mk}}$ and $e \star C \to (e \star C_{\mathrm{mk}})_{\mathrm{mk}}$. As the two codomain are marked, they are isomorphic.

The fact that will be used the most with the marked Segal A-precategory is their right lifting property with respect to morphisms of shape $[\tau_n^i(a), \Lambda^1[2]] \cup [a, 2] \to [\tau_n^i(a), 2]$. This fact will be used freely.

We recall that $[2] \otimes a$ is the following pushout:

$$\begin{array}{c} [1] \otimes a \amalg [1] \otimes a \xrightarrow{d^1 \otimes a \amalg d^2 \otimes a} [2] \otimes a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ e \star a \amalg e \star a \xrightarrow{d^1 \otimes a \amalg d^2 \otimes a} [2] \otimes a \end{array}$$

Definition 3.2.3.2. We define $[e, 1] \vee (e \star [a, 1])$ as the colimit of the following diagram

$$[e, 1] \vee [e \star a, 1] \xleftarrow{[d^0 \star a, 2]} [e, 1] \vee [a, 1] \xrightarrow{[a, d^2]} [e, 2] \vee [a, 1]$$

The canonical composite morphism

$$[e \star a, 1] \xrightarrow{[e \star a, d^1]} [e, 1] \vee [e \star a, 1] \to [e, 1] \vee (e \star [a, 1])$$

is also denoted by $[e \star a, d^1]$. Eventually, we define $[\overline{[1] \star [a, 1]}$ as the following pushout

$$\begin{array}{c} [1] \star \{0\} \longrightarrow [1] \star [a, 1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [2]_t \longrightarrow \overline{[1] \star [a, 1]} \end{array}$$

Lemma 3.2.3.3. There is a weak equivalence from $[\overline{[1] \star [a, 1]}$ to the colimit of the diagram

$$[[1] \star a, 1] \xleftarrow{[d^0 \star a, 1]} [e \star a, 1] \xrightarrow{[e \star a, d^1]} [e, 1] \vee (e \star [a, 1])$$

making $[\overline{[1] \star [a, 1]}$ the homotopy colimit of the previous diagram.

119