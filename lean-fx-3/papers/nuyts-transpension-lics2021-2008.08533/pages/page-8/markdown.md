16:8

A. Nuyts and D. Devriese

Vol. 20:2

Linear/affine shape variables:

|  FF:CTX-SHP\( \Gamma \) ctx\( \overline{\Gamma, u : \mathbb{U} \) ctx | FF:CTX-SHP:FMAP\( \sigma : \Gamma \to \Gamma' \)\( (\sigma, u/u') : (\Gamma, u : \mathbb{U}) \to (\Gamma', u' : \mathbb{U}) \) | FF:CTX-SHP:WKN (optional)\( \sigma : \Gamma \to \Gamma' \)\( \overline{\sigma : (\Gamma, u : \mathbb{U}) \to \Gamma'} \)  |
| --- | --- | --- |

Linear/affine function type:

|  FF:FORALL\( \Gamma, u : \mathbb{U} \vdash A \text{ type} \)\( \overline{\Gamma \vdash \forall u.A \text{ type}} \) | FF:FORALL:INTRO\( \Gamma, u : \mathbb{U} \vdash a : A \)\( \overline{\Gamma \vdash \lambda u.a : \forall u.A} \) | FF:FORALL:ELIM\( \Gamma \vdash f : \forall u.A \)No shape vars in \( \Delta \)\( \overline{\Gamma, u : \mathbb{U}, \delta : \Delta \vdash f u : A} \)  |
| --- | --- | --- |

Telescope quantification:

|  FF:CTX-FORALL\( \Gamma, u : \mathbb{U}, \delta : \Delta \text{ ctx} \)No shape vars in \( \Delta \)\( \overline{\Gamma, \forall u.(\delta : \Delta) \text{ ctx}} \) | FF:CTX-FORALL:FMAP\( (\sigma, u/u', \tau/\delta') : (\Gamma, u : \mathbb{U}, \delta : \Delta) \to (\Gamma', u' : \mathbb{U}, \delta' : \Delta') \)\( (\sigma, \lambda u.\tau/\lambda u'.\delta') : (\Gamma, \forall u.(\delta : \Delta)) \to (\Gamma', \forall u'.(\delta' : \Delta')) \)  |
| --- | --- |

FF:CTX-FORALL:NIL

\[
(\Gamma , \forall u. ()) = \Gamma
\]

FF:CTX-FORALL:FMAP:NIL

\[
(\sigma , \lambda u. () / \lambda u ^ {\prime}. ()) = \sigma
\]

Telescope application

|  FF:CTX-APP\( \Gamma, u : \mathbb{U}, \delta : \Delta \text{ ctx} \)\( (v/u, (\lambda u.\delta) v/\delta) : (\Gamma, \forall u.(\delta : \Delta), v : \mathbb{U}) \to (\Gamma, u : \mathbb{U}, \delta : \Delta) \)  |
| --- |

FF:CTX-APP:NAT : The following diagram commutes:

\[
\begin{array}{c} (\Gamma , \forall u. (\delta : \Delta), v: \mathbb {U}) \xrightarrow {(v / u , (\lambda u . \delta)   v / \delta)} (\Gamma , u: \mathbb {U}, \delta : \Delta) \\ \Biggl \downarrow_ {(\sigma , \lambda u. \tau / \lambda u ^ {\prime}. \delta^ {\prime}, v / v ^ {\prime})} \\ (\Gamma^ {\prime}, \forall u ^ {\prime}. (\delta^ {\prime}: \Delta^ {\prime}), v ^ {\prime}: \mathbb {U}) \xrightarrow [ (v ^ {\prime} / u ^ {\prime} , (\lambda u ^ {\prime} . \delta^ {\prime})   v ^ {\prime} / \delta^ {\prime}) ]{(v / u , (\lambda u . \delta)   v / \delta)} (\Gamma^ {\prime}, u ^ {\prime}: \mathbb {U}, \delta^ {\prime}: \Delta^ {\prime}) \end{array}
\]

FF:CTX-APP:NIL

\[
(v / u, (\lambda u. ()) v / ()) = (v / u)
\]

FF:CTX-FORALL:FMAP:CTX-APP

\[
(\lambda v. (\lambda u. \delta) v / \lambda u. \delta) = 1 _ {(\Gamma , \forall u. (\delta : \Delta))}
\]

Transpension type:

|  FF:TRANSP\( \Gamma, u : \mathbb{U}, \delta : \Delta \text{ ctx} \)\( \frac{\Gamma, \forall u.(\delta : \Delta) \vdash A \text{ type}}{\Gamma, u : \mathbb{U}, \delta : \Delta \vdash \Diamond[u] A \text{ type}} \) | FF:TRANSP:INTRO\( \frac{\Gamma, \forall u.(\delta : \Delta) \vdash a : A}{\Gamma, u : \mathbb{U}, \delta : \Delta \vdash \text{mer}[u] a : \Diamond[u] A} \) | FF:TRANSP:ELIM\( \frac{\Gamma, u : \mathbb{U} \vdash t : \Diamond[u] A}{\Gamma \vdash \text{unmer}(u.t) : A} \)  |
| --- | --- | --- |

FF:TRANSP:BETA

\[
\frac {\Gamma \vdash a : A}{\Gamma \vdash \operatorname{unmer} (u . \operatorname{mer} [ u ] a) = a : A}
\]

FF:TRANSP:ETA

\[
\begin{array}{l} \Gamma , u: \mathbb {U}, \delta : \Delta \vdash t: \Diamond [ u: \mathbb {U} ] A \\ \overline {{\Gamma , u : \mathbb {U} , \delta : \Delta \vdash t =}} \\ \operatorname{mer} [ u ] (\operatorname{unmer} (v. t [ v / u, (\lambda u. \delta) v / \delta ])) : \Diamond [ u ] A \end{array}
\]

FF:TRANSP:NAT

\[
\Gamma^ {\prime}, \forall u ^ {\prime}. (\delta^ {\prime}: \Delta^ {\prime}) \vdash A \text { type }
\]

\[
(\sigma , u / u ^ {\prime}, \tau / \delta^ {\prime}):
\]

\[
(\Gamma , u: \mathbb {U}, \delta : \Delta) \rightarrow (\Gamma^ {\prime}, u ^ {\prime}: \mathbb {U}, \delta^ {\prime}: \Delta^ {\prime})
\]

\[
\Gamma , u: \mathbb {U}, \delta : \Delta \vdash (\Diamond [ u ^ {\prime} ] A) [ \sigma , u / u ^ {\prime}, \tau / \delta^ {\prime} ] =
\]

\[
\left. \left\langle [ u ] \left(A [ \sigma , \lambda u. \tau / \lambda u ^ {\prime}. \delta^ {\prime} ]\right) \text {type} \right. \right.
\]

FF:TRANSP:INTRO:NAT

\[
\Gamma^ {\prime}, \forall u ^ {\prime}. (\delta^ {\prime}: \Delta^ {\prime}) \vdash a: A
\]

\[
(\sigma , u / u ^ {\prime}, \tau / \delta^ {\prime}):
\]

\[
(\Gamma , u: \mathbb {U}, \delta : \Delta) \rightarrow (\Gamma^ {\prime}, u ^ {\prime}: \mathbb {U}, \delta^ {\prime}: \Delta^ {\prime})
\]

\[
\Gamma , u: \mathbb {U}, \delta : \Delta \vdash (\operatorname{mer} [ u ^ {\prime} ] a) [ \sigma , u / u ^ {\prime}, \tau / \delta^ {\prime} ] =
\]

\[
\operatorname{mer} [ u ] \left(a [ \sigma , \lambda u. \tau / \lambda u ^ {\prime}. \delta^ {\prime} ]\right): (\left. \left\langle [ u ^ {\prime} ] A\right) [ \sigma , u / u ^ {\prime}, \tau / \delta^ {\prime} ] \right.
\]

Figure 1: Selection of typing rules for a fully faithful transpension type.