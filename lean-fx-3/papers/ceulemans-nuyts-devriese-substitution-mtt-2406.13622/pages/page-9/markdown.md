J. Ceulemans, A. Nuyts and D. Devriese

9

For atomic substitutions we have

\[
v \left[ \mathrm{id} ^ {\mathrm{a}} \right] _ {\text {asub,var}} ^ {\Lambda} = v \tag {22}
\]

\[
v \left[ \text { weaken } (\sigma) \right] _ {\text { asub,var }} ^ {\Lambda} = \left(v \left[ \sigma \right] _ {\text { asub,var }} ^ {\Lambda}\right) \left[ \pi . \Lambda \right] _ {\text { aren }} \tag {23}
\]

\[
v \left[ \sigma . \widehat {\mathbf {m}} _ {\mu} \right] _ {\text {asub,var}} ^ {\Lambda} = v \left[ \sigma \right] _ {\text {asub,var}} ^ {\widehat {\mathbf {m}} _ {\mu} \cdot \Lambda} \tag {24}
\]

\[
v \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\beta \in \Theta \Rightarrow \Psi} \right] _ {\text {asub,var}} ^ {\Lambda} = v \left[ \beta \star 1 _ {\text {locks} (\Lambda)} \right] _ {2 - \text {cell}} ^ {\Theta . \Lambda \Rightarrow \Psi . \Lambda} \tag {25}
\]

\[
\mathbf {v} _ {0} ^ {\alpha} [ \sigma . t ] _ {\text {asub,var}} ^ {\Lambda} = t \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \widehat {\mathbf {m}} _ {\mu} \Rightarrow \Lambda} \right] _ {\text {aren}} \tag {26}
\]

\[
\operatorname{suc} (v) [ \sigma . t ] _ {\text {asub,var}} ^ {\Lambda} = v [ \sigma ] _ {\text {asub,var}} ^ {\Lambda}. \tag {27}
\]

### 3.3 Relating WSMTT and SFMTT

We present the full definitions of the translation function  \( [\_] \)  from WSMTT to SFMTT and the embedding function  \( \text{embed}(\_) \)  in the converse direction. All interesting cases have been covered in the paper, but we include the definition here for easy reference.

#### Translation from WSMTT to SFMTT

\[
[ [ (\mu \mid A) \rightarrow B ] ] = (\mu \mid [ [ A ] ]) \rightarrow [ [ B ] ] \quad [ [! ] ] = \mathrm{id} \circledast !
\]

\[
\llbracket \lambda^ {\mu} (t) \rrbracket = \lambda^ {\mu} (\llbracket t \rrbracket) \quad \llbracket \mathrm{id} \rrbracket = \mathrm{id}
\]

\[
\llbracket \mathbf {v} _ {0} \rrbracket = \mathbf {v} _ {0} ^ {1 _ {\alpha}} \quad \llbracket \pi \rrbracket = \mathrm{id} \circledast \pi
\]

\[
\llbracket t [ \sigma ] _ {\mathrm{ws}} \rrbracket = \llbracket t \rrbracket [ \llbracket \sigma \rrbracket ] _ {\text {sub}} \quad \llbracket \sigma \circ \tau \rrbracket = \llbracket \sigma \rrbracket + + \llbracket \tau \rrbracket
\]

\[
[ [ \text { Bool } ] ] = \text { Bool } \quad [ [ \sigma . \widehat {\mathbf {m}} _ {\mu} ] ] = [ [ \sigma ]. \widehat {\mathbf {m}} _ {\mu}
\]

\[
[ [ \text {true} ] ] = \text {true} \quad \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi} \right] = \mathrm{id} \circledast \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi}
\]

\[
[ [ \text {false} ] ] = \text {false} \quad [ [ \sigma . t ] ] = [ [ \sigma ] ] ^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}. [ [ t ] ])
\]

\[
[ [ \text { if } (A; s; t; t ^ {\prime}) ] ] = \text { if } ([ [ A ] ]; [ [ s ] ]; [ [ t ] ]; [ [ t ^ {\prime} ] ])
\]

\[
\llbracket \mathsf {a p p} _ {\mu} (f; t) \rrbracket = \mathsf {a p p} _ {\mu} ([ [ f ] ]; [ [ t ] ])
\]

\[
[ [ \langle \mu \mid A \rangle ] ] = \langle \mu \mid [ [ A ] ] \rangle
\]

\[
\llbracket \operatorname{mod} _ {\mu} (t) \rrbracket = \operatorname{mod} _ {\mu} ([ [ t ] ])
\]

\[
\llbracket \operatorname{letmod} _ {\nu , \mu} (A; B; t; s) \rrbracket = \operatorname{letmod} _ {\nu , \mu} ([ [ A ] ]; [ [ B ] ]; [ [ t ] ]; [ [ s ] ])
\]

#### Embedding of SFMTT into WSMTT

For expressions we have the following.

\[
\operatorname{embed} \left(\mathbf {v} _ {0} ^ {\alpha}\right) = \mathbf {v} _ {0} \left[ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \widehat {\mathbf {m}} _ {\mu} \Rightarrow \Theta} \right] _ {\mathrm{ws}}
\]

\[
\operatorname{embed} (\operatorname{suc} (v)) = \operatorname{embed} (v) [ \pi . \Theta ] _ {\mathrm{ws}}
\]

\[
\operatorname{embed} (\text { Bool }) = \text { Bool }
\]

\[
\text { embed(true) } = \text { true }
\]

\[
\text { embed(false) } = \text { false }
\]

\[
\operatorname{embed} (\text { if } (A; s; t; t ^ {\prime})) = \text { if } (\operatorname{embed} (A); \operatorname{embed} (s); \operatorname{embed} (t); \operatorname{embed} (t ^ {\prime}))
\]