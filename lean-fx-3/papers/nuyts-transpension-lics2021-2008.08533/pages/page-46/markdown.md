16:46

A. NUYTS AND D. DEVRIESE

Vol. 20:2

Binary and destrictified reformulation of the original \(\Psi\)-type [BCM15, Mou16, CH21]:

\[
\Delta \vdash A _ {\epsilon} \text { type } \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , x _ {0}: A _ {0}, x _ {1}: A _ {1} \vdash R \text { type }
\]

\[
\Delta , i: \mathbb {I}, \theta : \Theta \vdash \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R) \text { type }
\]

\[
\text { where } \Psi_ {\epsilon} A _ {0} A _ {1} R = A _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta \vdash a _ {\epsilon}: A _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta \vdash r: R [ a _ {0} / x _ {0}, a _ {1} / x _ {1} ]
\]

\[
\Delta , i: \mathbb {I}, \theta : \Theta \vdash \operatorname{in} \Psi_ {i} a _ {0} a _ {1} r: \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R)
\]

\[
\text { where } \operatorname{in} \Psi_ {\epsilon} a _ {0} a _ {1} r = a _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , i: \mathbb {I} \vdash q = \operatorname{in} \Psi_ {i} q [ 0 / i ] q [ 1 / i ] (\operatorname{out} \Psi (j. q [ j / i ]))
\]

\[
\Delta , i: \mathbb {I} \vdash q: \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R)
\]

\[
\Delta \vdash \operatorname{out} \Psi (i. q): R [ q [ 0 / i ] / x _ {0}, q [ 1 / i ] / x _ {1} ]
\]

\[
\text { where } \operatorname{out} \Psi (i. \text { in } \Psi_ {i} a _ {0} a _ {1} r) = r
\]

#### Ψ-type in FFTraS:

\[
\Delta , \theta : \Theta [ \epsilon / i ] \vdash A _ {\epsilon} \text { type } \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , \forall i. (\theta : \Theta), x _ {0}: A _ {0} [ (\lambda i. \theta) 0 / \theta ], x _ {1}: A _ {1} [ (\lambda i. \theta) 1 / \theta ] \vdash R \text { type }
\]

\[
\Delta , i: \mathbb {I}, \theta : \Theta \vdash \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R) \text { type }
\]

\[
\text { where } \Psi_ {\epsilon} A _ {0} A _ {1} R = A _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , \theta : \Theta [ \epsilon / i ] \vdash a _ {\epsilon}: A _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
\Delta , \forall i. (\theta : \Theta) \vdash
\]

\[
r: R [ a _ {0} [ (\lambda i. \theta) 0 / \theta ] / x _ {0}, a _ {1} [ (\lambda i. \theta) 1 / \theta ] / x _ {1} ]
\]

\[
\Delta , i: \mathbb {I}, \theta : \Theta \vdash \operatorname{in} \Psi_ {i} a _ {0} a _ {1} r: \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R)
\]

\[
\text { where } \operatorname{in} \Psi_ {\epsilon} a _ {0} a _ {1} r = a _ {\epsilon} \quad (\epsilon \in \{0, 1 \})
\]

\[
q = \operatorname{in} \Psi_ {i} q [ 0 / i ] q [ 1 / i ] (\operatorname{out} \Psi (j. q [ j / i, (\lambda i. \theta) j / \theta ]))
\]

\[
\Delta , i: \mathbb {I} \vdash q: \Psi_ {i} A _ {0} A _ {1} (x _ {0}. x _ {1}. R)
\]

\[
\Delta \vdash \operatorname{out} \Psi (i. q): R [ q [ 0 / i ] / x _ {0}, q [ 1 / i ] / x _ {1} ]
\]

\[
\text { where } \operatorname{out} \Psi (i. \text { in } \Psi_ {i} a _ {0} a _ {1} r) = r
\]

#### Ψ-type in MTraS:

PSI

\[
\mathbb {X}, u: \mathbb {U} \mid \Gamma , _ {-}: u \in \partial \mathbb {U} \vdash A \text { type }
\]

\[
\mathbb {X} \mid \Gamma , \hat {x}: (-: u \in \partial \mathbb {U}) \rightarrow A, \widehat {\mathbf {u}} _ {[ [ u ]} ^ {\forall u} \vdash R \text { type }
\]

\[
\mathbb {X}, u: \mathbb {U} \mid \Gamma \vdash \Psi_ {u} A (\hat {x}. R) \text { type }
\]

\[
\text { where } \_: u \in \partial \mathbb {U} \vdash \Psi_ {u} A (\hat {x}. R) = A
\]

PSI:INTRO

\[
\mathbb {X}, u: \mathbb {U} \mid \Gamma , _ {-}: u \in \partial \mathbb {U} \vdash a: A
\]

\[
\mathbb {X} \mid \Gamma , \widehat {\mathbf {u}} _ {[ [ u ]} ^ {\forall u} \vdash r: R [ \lambda .. a / \hat {x}, \widehat {\mathbf {u}} _ {[ [ u ]} ^ {\forall u} ]
\]

\[
\mathbb {X}, u: \mathbb {U} \mid \Gamma \vdash \operatorname{in} \Psi_ {u} (- a) r: \Psi_ {u} A (\hat {x}. R)
\]

\[
\text { where } \_: u \in \partial \mathbb {U} \vdash \operatorname{in} \Psi_ {u} (- a) r = a
\]

\[
q = \operatorname{in} \Psi_ {u} (- q) \left(\operatorname{out} \Psi_ {\neg \forall u} q [ \widehat {\mathbf {a}} _ {\text {reidx} _ {u}} ^ {\text {app} _ {u}} ]\right)
\]

PSI:ELIM

\[
\mathbb {X}, u: \mathbb {U} \mid \Delta , \widehat {\mathbf {u}} _ {\forall u} ^ {\exists [ u ]} \vdash q: \Psi_ {u} A (\hat {x}. R)
\]

\[
\mathbb {X} \mid \Delta \vdash \operatorname{out} \Psi_ {\neg \forall u} q: R [ \lambda .. q / \hat {x}, \widehat {\mathbf {u}} _ {[ [ u ]} ^ {\forall u} ] [ \widehat {\mathbf {a}} _ {\text {unmer} _ {u}} ^ {\text {const} _ {u}} ]
\]

\[
\text { where } \operatorname{out} \Psi_ {\neg \forall u} \operatorname{in} \Psi_ {u} (- a) r = r [ \widehat {\mathbf {a}} _ {\text { unmer } _ {u}} ^ {\text { const } _ {u}} ]
\]

Figure 11: Typing rules for the  \( \Psi \) -type.

\((\lambda i.\theta)j / \theta\) in FFTraS give rise to usages of \(\widehat{\mathbf{a}}_{\mathrm{reidx}_u}^{\mathrm{app}_u}\) in MTraS. The usages of \(\widehat{\mathbf{a}}_{\mathrm{unmer}_u}^{\mathrm{const}_u}\) are entirely absent in FFTraS, but for \(\top\)-slice fully faithful multipliers, this is an isomorphism anyway.

The eliminator out \( \Psi \) only eliminates sections. For T-slice fully faithful and shard-free multipliers, the \( \Phi \)-rule provides a pattern-matching eliminator which lets us treat the boundary and section cases separately.

Theorem 10.2. For any multiplier, the \(\Psi\)-type in Fig. 11 is implementable from the transpension type and the strictness axiom.