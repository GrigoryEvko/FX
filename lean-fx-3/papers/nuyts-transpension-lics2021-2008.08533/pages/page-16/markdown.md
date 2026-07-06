16:16

A. NUYTS AND D. DEVRIESE

Vol. 20:2

### Context locking:

Note: We write  \( (\sigma,\mathbf{\Phi}_{\mu}) \)  as shorthand for  \( (\sigma,\mathbf{Q}_{1:\mu\Rightarrow\mu}) \) , an instance of LOCK:FMAP.

|  LOCK\( q \mid \Gamma \text{ ctx } \quad \mu : p \to q \) | LOCK:FMAP\( q \mid \sigma : \Gamma \to \Delta \quad \mu, \nu : p \to q \quad \alpha : \mu \Rightarrow \nu \)  |
| --- | --- |
|  \( p \mid \Gamma, \mathbf{\Phi}_{\mu} \text{ ctx} \) | \( p \mid (\sigma, \mathbf{Q}_{\alpha}) : (\Gamma, \mathbf{\Phi}_{\nu}) \to (\Delta, \mathbf{\Phi}_{\mu}) \)  |
|  where \( \Gamma = (\Gamma, \mathbf{\Phi}_{1}) \) | where \( \sigma = (\sigma, \mathbf{Q}_{1:1 \Rightarrow 1}) \quad (\sigma, \mathbf{Q}_{\alpha'}, \mathbf{Q}_{\alpha}) = (\sigma, \mathbf{Q}_{(\alpha' \star \alpha)}) \)  |
|  \( (\Gamma, \mathbf{\Phi}_{\nu}, \mathbf{\Phi}_{\mu}) = (\Gamma, \mathbf{\Phi}_{\nu \circ \mu}) \) | \( 1 = (1, \mathbf{Q}_{1:\mu \Rightarrow \mu}) \quad (\sigma, \mathbf{Q}_{\alpha}) \circ (\tau, \mathbf{Q}_{\beta}) = (\sigma \circ \tau, \mathbf{Q}_{(\beta \circ \alpha)}) \)  |

### Modal context extension:

We consider the non-modal rule CTX-EXT and its introduction, elimination and computation rules as a special case of CTX-MODEXT for p = q and  \( \mu = 1 \) .

|  CTX-MODEXT\( q \mid \Gamma \text{ ctx } \quad \mu : p \to q \)\( p \mid \Gamma, \mathbf{\Phi}_{\mu} \vdash T \text{ type } \)\( \overline{q \mid \Gamma, \mu \mid x : T \text{ ctx}} \) | CTX-MODEXT:INTRO\( q \mid \sigma : \Delta \to \Gamma \quad \mu : p \to q \)\( p \mid \Delta, \mathbf{\Phi}_{\mu} \vdash t : T[\sigma, \mathbf{\Phi}_{\mu}] \)\( \overline{q \mid (\sigma, t/x) : \Delta \to (\Gamma, \mu \mid x : T)} \)where \( \tau = ((x/\emptyset) \circ \tau, x[\tau, \mathbf{\Phi}_{\mu}] / x) \)\( (\sigma, t/x) \circ \rho = (\sigma \circ \rho, t[\rho, \mathbf{\Phi}_{\mu}] / x) \)  |
| --- | --- |
|  CTX-MODEXT:WKN\( q \mid \Gamma \text{ ctx } \quad \mu : p \to q \)\( p \mid \Gamma, \mathbf{\Phi}_{\mu} \vdash T \text{ type } \)\( \overline{q \mid (x/\emptyset) : (\Gamma, \mu \mid x : T) \to \Gamma} \)where \( (x/\emptyset) \circ (\sigma, t/x) = \sigma \) | CTX-MODEXT:VAR\( q \mid \Gamma \text{ ctx } \quad \mu : p \to q \)\( p \mid \Gamma, \mathbf{\Phi}_{\mu} \vdash T \text{ type } \)\( \overline{q \mid \Gamma, \mu \mid x : T, \mathbf{\Phi}_{\mu} \vdash x : T[(x/\emptyset), \mathbf{\Phi}_{\mu}]} \)where \( \Delta, \mathbf{\Phi}_{\mu} \vdash x[\sigma, t/x, \mathbf{\Phi}_{\mu}] = t : T[\sigma, \mathbf{\Phi}_{\mu}] \)  |

Figure 5: Structural rules of MTT [GKNB21][Nuy20a, fig. 5.5].

Adding locks (LOCK) is strictly functorial: it preserves identity and composition of modalities. In fact, it is strictly 2-functorial: it also has an action on 2-cells (LOCK:FMAP, producing substitutions between locked contexts) that preserves identity and composition of 2-cells. It is also strictly bifunctorial: we can combine a substitution and a 2-cell to a substitution between locked contexts. If the 2-cell is the identity, then we write \(\mathbf{\Phi}_{\mu}\) for \(\mathbf{Q}_{1:\mu \Rightarrow \mu}\).

A modal variable  \( \mu \mid x : T \)  introduced by CTX-MODEXT is essentially the same as a non-modal variable  \( \hat{x} : \langle \mu \mid T \rangle \)  (which in turn is shorthand for  \( 1 \mid \hat{x} : \langle \mu \mid T \rangle \) ), but the judgemental modal annotation allows direct access to a variable of type A through the variable rule. Hence, the type T is checked the same way as it would be in  \( \langle \mu \mid T \rangle \) . Terms t substituted for a modal variable x are also checked in the locked context, as if we would be substituting  \( mod_{\mu} t \)  instead. The variable rule does not produce  \( x : \langle \mu \mid T \rangle \)  but instead uses transposition to move the modality  \( \mu \)  to the left in the form of a lock. As such, it can be seen as implicitly involving a co-unit.

By analogy with CTX-EXT:VAR:LOOKUP, we would like a more general unofficial variable 'rule' that allows accessing a variable \( x \) that is buried under a general telescope \( \Delta \) rather than a single lock. By LOCK:FMAP, we can weaken under locks (which, like ordinary weakening, we will leave notationally implicit), so we can easily remove all variables from \( \Delta \) and then apply strict functoriality of LOCK to fuse the remaining locks, obtaining a single lock \( \mathbf{\Phi}_{\mathrm{locks}(\Delta)} \), where the modality \( \mathrm{locks}(\Delta) \) is defined as follows:

\[
\operatorname{locks} (\cdot) = 1, \quad \operatorname{locks} (\Delta , \mathbf {\Phi} _ {\mu}) = \operatorname{locks} (\Delta) \circ \mu , \quad \operatorname{locks} (\Delta , \mu \mid x: T) = \operatorname{locks} (\Delta).
\]