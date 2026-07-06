16:14

A. Nuyts and D. Devriese

Vol. 20:2

Judgement forms:

| p | Γ ctx | Γ is a context at mode p, |
| --- | --- | --- |
| p | σ : Δ → Γ | σ is a simultaneous substitution from Δ to Γ at mode p, |
| p | Γ ⊢ T type | T is a type in context Γ at mode p, |
| p | Γ ⊢ t : T | t has type T in context Γ at mode p. |

Figure 2: Judgement forms of MTT [GKNB21].

#### The type theory at each mode:

Basic rules of dependent type theory (including all desired types) at each mode q, e.g.:

| CTX-EMPTY | CTX-EXT | CTX-EXT:INTRO |
| --- | --- | --- |
| q mode | q | Γ ⊢ T type | q | σ : Δ → Γ q | Δ ⊢ t : T[σ] |
| q | · ctx | q | Γ, x : T ctx | q | (σ, t/x) : Δ → (Γ, x : T)where τ = ((x/∅) ∘ τ, x[τ]/x)(σ, t/x) ∘ ρ = (σ ∘ ρ, t[ρ]/x) |

|  CTX-EXT:WKN | CTX-EXT:VAR | SIGMA  |
| --- | --- | --- |
|  \( q \mid \Gamma \text{ ctx} \quad q \mid \Gamma \vdash T \text{ type} \) | \( q \mid \Gamma \text{ ctx} \quad q \mid \Gamma \vdash T \text{ type} \) | \( q \mid \Gamma \vdash A \text{ type} \)  |
|  \( q \mid (x/\emptyset) : (\Gamma, x : T) \to \Gamma \) | \( q \mid \Gamma, x : T \vdash x : T[(x/\emptyset)] \) | \( q \mid \Gamma, x : A \vdash B \text{ type} \)  |
|  where \( (x/\emptyset) \circ (\sigma, t/x) = \sigma \) | where \( x[\sigma, t/x] = t \) | \( q \mid \Gamma \vdash (x : A) \times B \text{ type} \)  |
|  UNI | UNI:ELIM | UNI:INTRO  |
|  \( q \mid \Gamma \text{ ctx} \quad \ell \in \mathbb{N} \) | \( q \mid \Gamma \vdash t : \mathsf{U}_{\ell}^{q} \) | \( q \mid \Gamma \vdash T \text{ type}_{\ell} \)  |
|  \( q \mid \Gamma \vdash \mathsf{U}_{\ell}^{q} \text{ type}_{\ell+1} \) | \( q \mid \Gamma \vdash \mathsf{El}(t) \text{ type}_{\ell} \) | \( q \mid \Gamma \vdash \lceil T \rceil : \mathsf{U}_{\ell}^{q} \)  |
|   | where \( \mathsf{El}(\lceil T \rceil) = T \) | where \( \lceil \mathsf{El}(t) \rceil = t \)  |

Figure 3: MTT includes all rules of ordinary DTT at each mode.

3.2. Judgement forms. The judgement forms of MTT are listed in Fig. 2. All forms are annotated with a mode p which specifies in what category they are to be interpreted. Every judgement form also has a corresponding equality judgement, which is respected by everything as the typing rules are to be read as a specification of a generalized algebraic theory (GAT [Car86, AK16]). The statements p mode and  \( \mu: p \rightarrow q \)  and  \( \alpha: \mu \Rightarrow \nu \)  are simply requirements about the mode theory. This means we give no syntax or equality rules for modalities and 2-cells: these are fixed by the choice of mode theory.

3.3. Typing rules. The typing rules are listed in Figs. 3 to 6 and discussed below.

3.3.1. The type theory at each mode. Since every mode corresponds to a model of all of dependent type theory (DTT), we start by importing all the usual typing rules of DTT, to be applied in MTT at any given fixed mode. Some examples of such rules are given in Fig. 3, where we have consciously included rules for non-modal context extension, even though these will be generalized to modal rules later on. One reason to do so is that other rules of DTT, such as SIGMA, depend on these and therefore cannot be imported without. Another is that this way, we have a warm-up towards the modal rules and in particular we