8:16

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese

record RRGraph : Type1 where
    field
    cr : Type
    lrel : cr → cr → Type
    requ : ∀ (a b : cr) → lrel a b ≈ Bridge a b
open RRGraph public

record DispRRG (Γ : RRGraph) : Type1 where
    field
    dcr : Γ .cr → Type
    dlrel : ∀ (γ₀ γ₁ : Γ .cr) (γr : Γ .lrel γ₀ γ₁) (a₀ : dcr γ₀) (a₁ : dcr γ₁) → Type
    drequ : (γ₀ γ₁ : Γ .cr) (γr : Γ .lrel γ₀ γ₁) (γγ : Bridge γ₀ γ₁) (γprf : γr [ (Γ .requ γ₀ γ₁) ] γγ)
    (a₀ : dcr γ₀) (a₁ : dcr γ₁) → dlrel γ₀ γ₁ γr a₀ a₁ ≈ BridgeP (λ x → dcr (γγ x)) a₀ a₁
open DispRRG public
→Form : ∀ {Γ : RRGraph} (A B : DispRRG Γ) → DispRRG Γ
→Form A B .dcr γ = (A .dcr γ → B . dcr γ)
→Form A B .dlrel γ₀ γ₁ γr f₀ f₁ = ∀ a₀ a₁ → (ar : A .dlrel γ₀ γ₁ γr a₀ a₁) → B .dlrel γ₀ γ₁ γr (f₀ a₀) (f₁ a₁)
→Form A B .drequ γ₀ γ₁ γr γγ γprf f₀ f₁ = flip compEquiv extentEquiv --under the hood: extent
((equivΠCod λ a₀ → equivΠCod λ a₁ →
    equivΠ' (A .drequ γ₀ γ₁ γr γγ γprf a₀ a₁) λ [ar] [aa] aprf →
    B .drequ γ₀ γ₁ γr γγ γprf (f₀ a₀) (f₁ a₁)))

Fig. 3. (Displayed) relativistic reflexive graphs in Agda --bridges, and their →FM semantic rule.

Structure Relatedness Principle (SRP): For each type \(\Gamma : \text{Type of Agda --bridges}\), (resp. type family \(T : \Gamma \to \text{Type}\)) the Bridge type of \(\Gamma\) (resp. the BridgeP type of \(T\)) can be characterized as a type of logical relations (resp. heterogeneous logical relations).

In other words, the SRP conveys the idea that bridges act as logical relations at all types*. For instance the SRP holds at Type thanks to the relativity theorem of Section 2.5, and the SRP holds at function types \((a:A)\to B\) thanks to the extentEquiv theorem of Section 2.4.

Contrary to bare parametricity, the SRP can not be stated as an object-level theorem of Agda --bridges. The reason is that types of logical relations are ad hoc: there is a priori no Agda --bridges function Lrel : Type → Type acting as an internal parametricity translation, computing for each  \( \Gamma \)  its type of logical relations Lrel  \( \Gamma \) . Indeed parametricity translations are defined by induction on the syntax, so using a type-casing operation. But having a first-class type-casing operator on types would contradict the internal parametricity of Agda --bridges! This means that the quantification (*) must be stated metatheoretically.

Since the SRP can not be obtained as a theorem, we package it as a definition on types (or type families). For reasons explained hereafter, types that satisfy the SRP are called relativistic reflexive graphs (RRG). Moreover type families  \( T : \Gamma \rightarrow Type \)  satisfying the SRP are called displayed relativistic reflexive graphs (dRRG). In what follows RRGs and dRRGs are defined in plain English. The corresponding formal Agda --bridges definitions of these structures are provided in Fig. 3.

Recall that we use a postfix \( r \) notation to denote (potentially heterogeneous) logical relations \( ar \) and a double-letter notation \( aa \) to denote (potentially dependent) bridges. Additionally, note that we use the notation \( a_0[e]a_1 \) to signify that \( e.fst a_0\equiv_{A_1}a_1 \) where \( e:A_0\simeq A_1 \) and \( a_0:A_0,a_1:A_1 \).

Definition 3.1 (Relativistic reflexive graph (RRG)). A relativistic reflexive graph is a type \(\Gamma : \text{Type}\) which, for all elements \(\gamma_0, \gamma_1 : \Gamma\), is equipped with a type denoted \(\Gamma\{\gamma_0, \gamma_1\} : \text{Type}\) and an equivalence denoted \(\eta^\Gamma : \Gamma\{\gamma_0, \gamma_1\} \simeq \text{Bridge}_\Gamma \gamma_0 \gamma_1\).

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.