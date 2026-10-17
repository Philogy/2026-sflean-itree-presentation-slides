import VersoSlides

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "Interaction Trees in Lean 4" =>

# Fuel vs. Relational Semantics

* Fuel: `eval : Nat → Prog → Option Result` (runs, but "out of fuel" is not divergence)
* Relational: `Prog → Result → Prop` (precise, but you can't run it)

# ITrees: `ret`, `tau`, `vis`

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

# Monad Instance and `#eval`

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
