34

Martin-Löf's type theory

# **Rules 2.1.37 (Rules for products).**

FORMATION

$$\frac{\Vdash A = A' \text{ type} \quad a : A \gg B = B' \text{ type}}{\Vdash (a : A) \times B = (a : A') \times B' \text{ type}}$$

INTRODUCTION

$$\frac{\Vdash A \text{ type} \quad a : A \gg B \text{ type} \quad \Vdash M = M' \in A \quad \Vdash N = N' \in B [M/a]}{\Vdash \langle M, N \rangle = \langle M', N' \rangle \in (a : A) \times B}$$

ELIMINATION-FST

$$\frac{\Vdash P = P' \in (a : A) \times B}{\Vdash \text{fst}(P) = \text{fst}(P') \in A}$$

ELIMINATION-SND

$$\frac{\Vdash P = P' \in (a : A) \times B}{\Vdash \text{snd}(P) = \text{snd}(P') \in B [\text{fst}(P)/a]}$$

REDUCTION-FST

$$\frac{\Vdash M \in A}{\Vdash \text{fst}(\langle M, N \rangle) = M \in A}$$

REDUCTION-SND

$$\frac{\Vdash N \in B [M/a]}{\Vdash \text{snd}(\langle M, N \rangle) = N \in B [M/a]}$$

UNIQUENESS

$$\frac{\Vdash P \in (a : A) \times B}{\Vdash P = \langle \text{fst}(P), \text{snd}(P) \rangle \in (a : A) \times B}$$

### 2.1.5.3 Natural numbers

The natural numbers will be our paradigmatic example of an inductive type, a type whose elements those constructible from a specified set of operators. (Eventually, they will be one particularly trivial instance of the schema for higher inductive types introduced in Part II.) The two introduction rules provide the two ways of constructing a natural number: zero is a natural, and the successor of any natural is again a natural number.

# **Rules 2.1.38 (Formation and introduction for natural numbers).**

FORMATION

$$\Vdash \text{Nat type}$$

INTRODUCTION-ZERO

$$\Vdash \text{zero} \in \text{Nat}$$

INTRODUCTION-SUC

$$\frac{\Vdash N = N' \in \text{Nat}}{\Vdash \text{suc}(N) = \text{suc}(N') \in \text{Nat}}$$

Rather than a projection rule in the vein of function or product types, elimination from the natural numbers is accomplished by an *induction principle*: to construct a dependent function from Nat into some type family $n : \text{Nat} \gg B$ type, we describe what to do in the zero and suc cases. As shown in the first rule of Rules 2.1.39 below, that data comes in the form of a term $Z \in B[\text{zero}/n]$, explaining what to do with zero, and a parameterized term $n : \text{Nat}, b : B \gg S \in B[\text{suc}(n)/n]$, explaining what to do with $\text{suc}(n)$ given a natural $n$ and the result $b$ of recursively applying the eliminator to $n$.