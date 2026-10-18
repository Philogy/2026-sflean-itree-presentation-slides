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
#[tokio::main]
async fn main() -> ! {
    loop {
        let request = next_connection().await;
        respond(request).await;
    }
}
```

* Non-Determinism and Undefined Behavior
```code rust
let layout = Layout::from_size_align(size_of::<u32>(), align_of::<u32>()).unwrap();
let p = unsafe { alloc(layout) } as *mut u32;
unsafe { *p.add(1) = 2 }; // UB: out of bounds
```


# Formalized Language Semantics: The Obvious Ways

:::table +colHeaders +rowHeaders +stripedRows +headerSep
*
  *
  * Fueled Interpreter
  * Big-Step Relation
  * Small-step relation
*
  * Shape
  * `eval : Nat → Prog → Option Val`
  * `inductive Eval : Prog → Val → Prop`
  * `inductive Step : Cfg → Cfg → Prop`
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
