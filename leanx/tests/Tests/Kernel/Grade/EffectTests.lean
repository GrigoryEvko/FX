import FX.Kernel.Grade.Effect

/-!
# Effect dimension tests
-/

namespace Tests.Kernel.Grade.Effect

open FX.Kernel
open FX.Kernel.Effect

/-! ## `tot` is empty -/

example : tot.io    = false := rfl
example : tot.div   = false := rfl
example : tot.ghost = false := rfl
example : tot.exn   = false := rfl
example : tot.alloc = false := rfl
example : tot.read  = false := rfl
example : tot.write = false := rfl
example : tot.async = false := rfl

/-! ## Singleton constructors -/

example : io_.io    = true := rfl
example : io_.div   = false := rfl
example : div_.div  = true := rfl
example : alloc_.alloc = true := rfl
example : ghost_.ghost = true := rfl
example : exn_.exn  = true := rfl
example : read_.read  = true := rfl
example : read_.write = false := rfl
example : write_.read  = true := rfl
example : write_.write = true := rfl
example : async_.async = true := rfl

/-! ## Add preserves the OR structure -/

example : (add io_ alloc_).io    = true := rfl
example : (add io_ alloc_).alloc = true := rfl
example : (add io_ alloc_).read  = false := rfl

example : add tot io_ = io_ := rfl
example : add io_ tot = io_ := rfl
example : add io_ io_ = io_ := rfl

/-! ## Laws -/

example : ∀ a b : Effect, add a b = add b a := Effect.add_comm
example : ∀ a b c : Effect, add (add a b) c = add a (add b c) := Effect.add_assoc
example : ∀ a : Effect, add a a = a := Effect.add_idem
example : ∀ a : Effect, add tot a = a := Effect.tot_add
example : ∀ a : Effect, add a tot = a := Effect.add_tot

/-! ## LessEq -/

example : LessEq tot io_ := by decide
example : ¬ LessEq io_ tot := by decide
example : LessEq io_ (add io_ alloc_) := by decide
example : LessEq read_ write_ := by decide    -- read ≤ write via union

/-! ## Subsumption preorder -/

example : ∀ a : Effect, LessEq a a := LessEq.refl
example : ∀ a b c : Effect, LessEq a b → LessEq b c → LessEq a c :=
  fun _ _ _ => LessEq.trans

/-! ## Surface-name bridge (A12) -/

-- `fromName?` recognizes each §9.4 built-in, returning the
-- singleton with `write_` already saturated per §9.3.
example : fromName? "IO"    = some io_    := rfl
example : fromName? "Div"   = some div_   := rfl
example : fromName? "Ghost" = some ghost_ := rfl
example : fromName? "Exn"   = some exn_   := rfl
example : fromName? "Alloc" = some alloc_ := rfl
example : fromName? "Read"  = some read_  := rfl
example : fromName? "Write" = some write_ := rfl
example : fromName? "Async" = some async_ := rfl

-- Unknown labels (user-defined §9.5 effects) return none —
-- elaborator falls back to string subset over these.
example : fromName? "Network"  = none := rfl
example : fromName? "State"    = none := rfl
example : fromName? "iosucks!" = none := rfl

-- `fromNames` splits names into (builtin-union, unknown-list).
example : fromNames [] = (tot, []) := rfl
example : fromNames ["IO"] = (io_, []) := rfl
example : (fromNames ["IO", "Alloc"]).1 = add alloc_ io_ := rfl
example : (fromNames ["Network", "State"]).2 = ["State", "Network"] := rfl
example : (fromNames ["IO", "Network", "Alloc"]).1 = add alloc_ io_ := rfl
example : (fromNames ["IO", "Network", "Alloc"]).2 = ["Network"] := rfl

-- Duplicate unknown names collapse — no spam in the residual list.
example : (fromNames ["Foo", "Foo"]).2 = ["Foo"] := rfl

/-! ## `Read ≤ Write` via saturation (§9.3) -/

-- A declared `Write` row subsumes a body row using only `Read`
-- because `write_`'s record pre-includes `read := true`.
example : subsumes read_ write_ = true := rfl

-- Reverse fails — Write is strictly stronger than Read.
example : subsumes write_ read_ = false := rfl

-- `Write` is subsumed by itself (tautological).
example : subsumes write_ write_ = true := rfl

-- Unrelated labels don't subsume each other.
example : subsumes io_ alloc_ = false := rfl
example : subsumes alloc_ io_ = false := rfl

-- Tot (empty row) is subsumed by everything.
example : subsumes tot io_ = true := rfl
example : subsumes tot (add io_ alloc_) = true := rfl

-- Nothing subsumes Tot except Tot itself.
example : subsumes io_ tot = false := rfl
example : subsumes tot tot = true := rfl

/-! ## Widening-name diagnostic builder -/

-- No widening when body ≤ declared.
example : wideningNames read_ write_ = [] := rfl
example : wideningNames tot io_ = [] := rfl

-- Single-label widening: body uses Write, declared only has Read.
example : wideningNames write_ read_ = ["Write"] := rfl

-- Multi-label widening sorted in spec order.
example :
    wideningNames (add io_ (add async_ write_)) read_ = ["IO", "Write", "Async"] := rfl

-- IO widening without affecting Read/Write bits.
example : wideningNames io_ alloc_ = ["IO"] := rfl

end Tests.Kernel.Grade.Effect
