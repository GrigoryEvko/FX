11:6

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

verbatim to mode $m$. Hence, the only pragmatic option is to introduce an operation that allows a context to be mapped to another mode.

**Forming a modal type.** There are several different proposed solutions to this problem in the literature [PD01, Clo18]. We will use a *Fitch-style* discipline [BGM17, BCM$^{+}$20, GSB19a]: we will require that a modality $\mu$ induce an operation on contexts in the *opposite* direction. We will denote this operation by a *lock*:

$$\begin{array}{c} \text{CX/LOCK} \\ \hline \Gamma \text{ ctx @ } m \\ \hline \Gamma, \text{ } \mu \text{ ctx @ } n \end{array}$$

Intuitively, $\text{ } \mu$ will behave somewhat like a left adjoint to $\langle \mu \mid - \rangle$. However, $\langle \mu \mid - \rangle$ acts on types while $-, \text{ } \mu$ acts on contexts, so this cannot be an ordinary adjunction. Instead, $\langle \mu \mid - \rangle$ will be what [BCM$^{+}$20] call a *dependent right adjoint* (DRA). A DRA essentially consists of a type former $\mathbf{R}$ and a context operation $\mathbf{L}$ such that

$$\{ N \mid \mathbf{L}(\Gamma) \vdash N : A \} \cong \{ M \mid \Gamma \vdash M : \mathbf{R}(A) \} \quad (\dagger)$$

See [BCM$^{+}$20] for a formal definition.

Just as with DRAs, the MTT formation and introduction rules for modal types effectively *transpose* types and terms across this adjunction:

$$\begin{array}{c c} \text{TP/MODAL} & \text{TM/MODAL-INTRO} \\ \mu : m \rightarrow n \quad \Gamma, \text{ } \mu \vdash A \text{ type}_\ell @ n & \mu : m \rightarrow n \quad \Gamma, \text{ } \mu \vdash M : A @ n \\ \hline \Gamma \vdash \langle \mu \mid A \rangle \text{ type}_\ell @ m & \Gamma \vdash \text{ mod}_\mu(M) : \langle \mu \mid A \rangle @ m \end{array}$$

It remains to show how to eliminate modal types. Previous work on Fitch-style calculi [BCM$^{+}$20, GSB19a] has employed elimination rules which essentially invert the introduction rule TM/MODAL-INTRO. Such rules *remove* one or more locks from the context during type-checking, and sometimes even trim a part of it. For example, a rule of this sort would be

$$\frac{\text{ } \mu \notin \Gamma' \quad \Gamma \vdash M : \langle \mu \mid A \rangle @ m}{\Gamma, \text{ } \mu, \Gamma' \vdash \text{ open}(M) : A @ n}$$

This kind of rule tends to be unruly, and delicate work is required to prove even basic results about it. For example, see the technical report [GSB19b] for a particularly laborious proof of the admissibility of substitution. The results in *op. cit.* could not possibly reuse any of the work of [BCM$^{+}$20], as a small change in the syntax leads to many subtle differences in the metatheory. Consequently, it seems unlikely that one could adapt this approach to a modality-agnostic setting like ours.

We will use a different technique, which is reminiscent of dual-context calculi [Kav20]. First, we will let the variable rule control the use of modal variables. Then, we will take a 'modal cut' rule, which will allow the substitution of modal terms for modal variables, to be our modal elimination rule.

**Accessing a modal variable.** The behavior of modal types can often be clarified by asking a simple question: when can we use a variable $x : \langle \mu \mid A \rangle$ of modal type to construct a term of type $A$? In previous Fitch-style calculi we would use the modal elimination rule to reduce the goal to $\langle \mu \mid A \rangle$, and then—*had the modal elimination rule not eliminated $x$ from the context*—we would simply use the variable. We may thus write down a term of type $A$ using