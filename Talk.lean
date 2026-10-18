module
public import VersoSlides

open VersoSlides

set_option verso.code.warnLineLength 500
set_option linter.unusedVariables false

#doc (Slides) "Representing Non-Terminating Computation using iTrees" =>

# What do we need to verify Real World Software?

* A Piece of Real World Software
* {fragment (style := embolden)}[A Language Specification]
* A Behavioral Specification

# Real Languages are Messy

* Effects
```code rust
let config = fs::read_to_string("config.toml")?;
fs::write("config.bak", &config)?;
```

* Non-Termination

```code rust
loop {
    let request = next_connection().await;
    respond(request).await;
}
```

* Non-Determinism and Undefined Behavior
```code rust
let mut x = Box::new(0u32);
unsafe { *Box::as_mut_ptr(&mut x).add(1) = 2 }; // UB: out of bounds
```

# Our Toy Language

:::class "big-code"
```code haskell
e ::= n | x | e + e | e - e | e < e
    | load e | alloc e                -- alloc: any free address
    | read                            -- effect: external input

s ::= skip | x := e | let x := e in s | s ; s
    | if e then s else s | while e do s
    | store e e | print e             -- effects
```
:::

:::class "big-code"
```code haskell
n := read;
let p := alloc 0 in
while 0 < n do
  store p (load p + n);
  print (load p);
  n := n - 1
```
:::

# Fueled Interpreter

:::class "big-code"
```code haskell
def exec : (fuel : Nat) → (input : Trace → Nat)
         → Stmt → State
         → Result State × Trace

| 0,   _,   s,           σ => (outOfFuel, [])     -- diverged? or unlucky?
| n+1, inp, while c s,   σ => if ⟦c⟧σ ≠ 0 then exec n inp (s ; while c s) σ …
| n+1, inp, x := read,   σ => let v := inp trace …   -- the world, pre-seeded
| n+1, inp, x := alloc e, σ => let ℓ := fresh σ …    -- one address, picked by us
```
:::

* Out of fuel ≠ divergence: a server and a crash look alike
* Nondeterminism must be resolved up front (oracles, `fresh`)

# Relational Big-Step

:::class "big-code"
```code haskell
inductive BigStep : Stmt → State → State → Trace → Prop   -- ⟨s, σ⟩ ⇓ ⟨σ', t⟩
```
:::

:::class "big-code"
```code haskell
⟨s₁, σ⟩ ⇓ ⟨σ₁, t₁⟩    ⟨s₂, σ₁⟩ ⇓ ⟨σ₂, t₂⟩        ⟨e, σ⟩ ⇓ v    σ.heap ℓ = none
──────────────────────────────────────        ───────────────────────────────────────
     ⟨s₁ ; s₂, σ⟩ ⇓ ⟨σ₂, t₁ ++ t₂⟩             ⟨x := alloc e, σ⟩ ⇓ ⟨σ[ℓ ↦ v][x ↦ ℓ], []⟩

                         ───────────────────────────────────
                          ⟨x := read, σ⟩ ⇓ ⟨σ[x ↦ v], [in v]⟩
```
:::

* Nondeterminism is free: any `ℓ`, any `v`
* `while true do print 1` has *no* derivation: the server is a no-op
* Fix: a second, coinductive judgment `⟨s, σ⟩ ⇑ T`, duplicating every rule

# Small-Step

:::class "big-code"
```code haskell
abbrev Cfg := Stmt × State                          -- the program is part of the config
inductive Step  : Cfg → Option Event → Cfg → Prop   -- none = silent τ step
inductive Steps : Cfg → Trace → Cfg → Prop          -- collect the labels
```
:::

:::class "big-code"
```code haskell
⟨while c s, σ⟩  ─τ→      ⟨if c then (s ; while c s) else skip, σ⟩
⟨print e, σ⟩    ─out v→  ⟨skip, σ⟩                    if ⟦e⟧σ = v
⟨s₁ ; s₂, σ⟩    ─ℓ→      ⟨s₁' ; s₂, σ'⟩               if ⟨s₁, σ⟩ ─ℓ→ ⟨s₁', σ'⟩
```
:::

* Infinite runs are infinite chains: the server finally exists
* Price: congruence rules everywhere, simulation diagrams up to τ



# Formalized Language Semantics: The Obvious Ways

:::table +colHeaders +rowHeaders +stripedRows +headerSep
*
  *
  * Fueled Interpreter
  * Big-Step Relation
  * Small-step relation
*
  * Shape
  * `eval : Nat → Oracles → Prog → Result (Val × Trace)`
  * `inductive Eval : Prog → Trace → Val → Prop`
  * `inductive Step : Cfg → Event → Cfg → Prop`
*
  * Executable?
  * ✅
  * ❌
  * ❌
*
  * Non-termination
  * Confused with "out of fuel"
  * Invisible (no derivation)
  * Infinite step chain
*
  * Effects & I/O
  * Ad hoc
  * Awkward
  * Labelled transitions
*
  * Proof style
  * Fuel lemmas everywhere
  * Induction on derivations
  * Simulation diagrams
:::


# Monad Instance and `#eval`

```lean
inductive Step (E : Type → Type) (R X : Type) : Type 1 where
  | ret (r : R)
  | tau (next : X)
  | vis {A : Type} (e : E A) (k : A → X)

/-- An ITree as a coalgebra: a hidden state and one observable step. -/
structure ITree (E : Type → Type) (R : Type) : Type 1 where
  σ : Type
  now : σ
  step : σ → Step E R σ

def ITree.spin : ITree E R := ⟨Unit, (), fun _ => .tau ()⟩
```

* Placeholder: infinite behaviour as a value, effects as an open signature `E`

```lean
inductive Out : Type → Type where
  | print (n : Nat) : Out Unit

def ITree.run (fuel : Nat) (t : ITree Out R) : List Nat × Option R :=
  go fuel t.now
where
  go : Nat → t.σ → List Nat × Option R
    | 0, _ => ([], none)
    | n + 1, s =>
      match t.step s with
      | .ret r => ([], some r)
      | .tau s' => go n s'
      | .vis (.print k) cont =>
        let (out, r) := go n (cont ())
        (k :: out, r)

def countdown : ITree Out Unit where
  σ := Nat
  now := 3
  step
    | 0 => .ret ()
    | n + 1 => .vis (.print (n + 1)) (fun _ => n)

#eval countdown.run 10
```

* Placeholder: `bind`, monad laws up to `eutt`

# `eutt` and Malloc-Agnostic `Same`

* Placeholder: weak bisimulation, finite `tau`s skipped, divergence preserved
* Placeholder: `Same` quantifies over all allocator placements

# CoFree and the Quotient

* Placeholder: CoFree + Step encoding, lawful monad on the bisimulation quotient

# Case Study: SIR

* Placeholder: Plank's SIR semantics as ITrees; passes preserve `Same`

# Takeaway

* Placeholder: executable *and* reasoned-about semantics in one definition
