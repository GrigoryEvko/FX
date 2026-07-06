5:32

E. CAVALLO AND R. HARPER

Vol. 17:4

special case directly for simplicity's sake. The importance of bool* arises from the fact that elements of a pointed type X* are in correspondence with pointed maps bool* → X*. As such, we can use naturality conditions with respect to functions bool* → X* to “probe” the behavior of a function polymorphic in pointed types, as we will see in Lemma 3.27.

Lemma 3.26 (Smash of booleans). bool* ∧ bool* is isomorphic to bool*; in particular, any element of bool* ∧ bool* is path-equal to either ⟨tt, tt⟩ or ⟨ff, ff⟩.

Proof. In one direction, we define F ∈ bool → bool* ∧ bool* to send tt to ⟨tt, tt⟩ and ff to ⟨ff, ff⟩. In the other, we define G ∈ bool* ∧ bool* → bool to send ⟨ff, ff⟩ to ff and all other constructors to tt. Clearly G ∘ F is the identity. For the other inverse condition, we show (s:bool* ∧ bool*) → Pathbool*∧bool*(s, F(Gs)) by smash product induction as follows.

▷ Case ⟨tt, tt⟩: Reflexivity.
▷ Case ⟨tt, ff⟩:
λ¹y.hcom₀∼₁bool*∧bool* (spokeᴸ(tt, y); y = 0 ⇔ x.spokeᴸ(ff, x), y = 1 ⇔ ...⟨tt, tt⟩).
▷ Case ⟨ff, ff⟩: Reflexivity.
▷ Case ⊗ᴸ: λ¹y.spokeᴸ(tt, y).
▷ Case spokeᴸ(tt, x): connectbool*∧bool*(λ¹y.spokeᴸ(tt, y))@x.
▷ Case spokeᴸ(ff, x):
λ¹y.hcom₀∼ₓbool*∧bool* (spokeᴸ(tt, y); y = 0 ⇔ x.spokeᴸ(ff, x), y = 1 ⇔ ...⟨tt, tt⟩).

The cases for ⟨tt, ff⟩, ⊗ᴿ, and spokeᴿ are obtained by taking the cases for ⟨ff, tt⟩, ⊗ᴸ, and spokeᴸ respectively and replacing spokeᴸ with spokeᴿ everywhere.

The following result, which characterizes terms F ∈ (A*, B*:Uₚₜ) → A → B → A* ∧ B*, is the linchpin of the argument; all uses of internal parametricity in the final results factor through this lemma. As we only use internal parametricity with relations that are graphs of functions, this result may also be cast as a corollary of the naturality of such terms, a special case of parametricity. In particular, we use the following naturality square for a : A and b : B, where [c]* ∈ bool* → C* is the pointed function sending tt to c₀ and ff to c.

$$\begin{array}{c} \mathsf{bool} \times \mathsf{bool} \xrightarrow{F \mathsf{bool}_* \mathsf{bool}_*} \mathsf{bool}_* \wedge \mathsf{bool}_* \\ [a] \times [b] \Biggl\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ A \times B \xrightarrow[FA_* B_*} A_* \wedge B_* \end{array}$$

Lemma 3.27 (Workhorse lemma). Let F ∈ (A*, B*:Uₚₜ) → A → B → A* ∧ B*. Then F is path equal to one of the following.

▷ λ...λ...λa.λb.⟨a, b⟩.
▷ λA*.λB*.λ...λ...⟨a₀, b₀⟩.

Proof. We show that the identity of F is determined by the value of F(bool*)(bool*)(ff)(ff). Let A*: Uₚₜ, B*: Uₚₜ, a : A, and b : B be given.

We have a function [a]* ∈ bool* → A* sending tt to a₀ and ff to a, likewise [b]* ∈ bool* → B* sending tt to b₀ and ff to b. Abstract a bridge variable x : I. We abbreviate G*a := Gr*a(bool*, A*, [a]*) and G*b := Gr*a(bool*, B*, [b]*). Applying F at G*a and G*b, we have the following.

$$FG_*^a G_*^b(\mathsf{gel}_x(\mathsf{ff}, a, \lambda^\mathbb{I}...a))(\mathsf{gel}_x(\mathsf{ff}, b, \lambda^\mathbb{I}...b)) \in G_*^a \wedge G_*^b$$