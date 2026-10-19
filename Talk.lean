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
unsafe { *Box::as_mut_ptr(&mut x).add(1) = 2 };
```

# Our Toy Language

*Definition*

```lean
inductive Expr where
  | lit (n: Nat) | var (id: Nat)
  | add (x y : Expr) | sub (x y : Expr) | lt (x y : Expr)
  | ref (v : Expr) | deref (addr : Expr)
  | read

inductive Stmt where
  | assign (id : Nat) (v : Expr)
  | ifThenElse (cond : Expr) (zero : List Stmt) (nonZero : List Stmt)
  | while (cond : Expr) (body : List Stmt)
  | store (addr v : Expr)
  | print (v : Expr)

abbrev Program := List Stmt
```

*Example Program*

:::class "big-code"
```code toy
n := read;
p := ref 0;
while 0 < n do
  store p (deref p + n);
  print (deref p);
  n := n - 1
```
:::


# Fueled Interpreter

:::class "big-code"
```code toy
def exec : (fuel : Nat) → (input : Trace → Nat)
         → Stmt → State
         → Result State × Trace

| 0,   _,   s,           σ => (outOfFuel, [])     -- diverged? or unlucky?
| n+1, inp, while c s,   σ => if ⟦c⟧σ ≠ 0 then exec n inp (s ; while c s) σ …
| n+1, inp, x := read,   σ => let v := inp trace …   -- the world, pre-seeded
| n+1, inp, x := ref e,  σ => let ℓ := fresh σ …     -- one address, picked by us
```
:::

* Out of fuel ≠ divergence: a server and a crash look alike
* Nondeterminism must be resolved up front (oracles, `fresh`)

# Relational Big-Step

:::class "big-code"
```code toy
inductive BigStep : Stmt → State → State → Trace → Prop   -- ⟨s, σ⟩ ⇓ ⟨σ', t⟩
```
:::

:::class "big-code"
```code toy
⟨s₁, σ⟩ ⇓ ⟨σ₁, t₁⟩    ⟨s₂, σ₁⟩ ⇓ ⟨σ₂, t₂⟩        ⟨e, σ⟩ ⇓ v    σ.heap ℓ = none
──────────────────────────────────────        ────────────────────────────────────────
     ⟨s₁ ; s₂, σ⟩ ⇓ ⟨σ₂, t₁ ++ t₂⟩             ⟨x := ref e, σ⟩ ⇓ ⟨σ[ℓ ↦ₕ v][x ↦ ℓ], []⟩

                         ───────────────────────────────────
                          ⟨x := read, σ⟩ ⇓ ⟨σ[x ↦ v], [in v]⟩
```
:::

* Nondeterminism is free: any `ℓ`, any `v`
* `while true do print 1` has *no* derivation: the server is a no-op
* Fix: a second, coinductive judgment `⟨s, σ⟩ ⇑ T`, duplicating every rule

# Small-Step

:::class "big-code"
```code toy
abbrev Cfg := Stmt × State                          -- the program is part of the config
inductive Step  : Cfg → Option Event → Cfg → Prop   -- none = silent τ step
inductive Steps : Cfg → Trace → Cfg → Prop          -- collect the labels
```
:::

:::class "big-code"
```code toy
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
  * Executable?
  * ✅
  * ❌
  * ❌
*
  * Non-termination
  * Akward quantification over `fuel`
  * Stuck State (or UB)
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


# What does our Ideal Version look like?

* Executable
* Reads like Straight-line Code
* Represents Non-Terminating Computation
* Less Bug-Prone

# Introducing Interaction Trees (iTrees)

An iTree based interpreter

```lean -show
namespace Interp

/-- One observable step: finish with `r`, take a silent step, or perform `e` and continue with `k`. -/
inductive Step (E : Type → Type) (R X : Type) : Type 1 where
  | ret (r : R)
  | tau (next : X)
  | vis {A : Type} (e : E A) (k : A → X)

/-- An ITree as a coalgebra: a hidden state and one observable step. -/
structure ITree (E : Type → Type) (R : Type) : Type 1 where
  σ : Type
  now : σ
  step : σ → Step E R σ

namespace ITree

def ret (r : R) : ITree E R := ⟨Unit, (), fun _ => .ret r⟩

/-- Run `t`; once it returns `a`, take one silent step into `g a`. -/
def bind (t : ITree E A) (g : A → ITree E B) : ITree E B where
  σ := t.σ ⊕ (Σ a, (g a).σ)
  now := .inl t.now
  step
    | .inl s => match t.step s with
      | .ret a => .tau (.inr ⟨a, (g a).now⟩)
      | .tau s' => .tau (.inl s')
      | .vis e k => .vis e (fun x => .inl (k x))
    | .inr ⟨a, s⟩ => match (g a).step s with
      | .ret b => .ret b
      | .tau s' => .tau (.inr ⟨a, s'⟩)
      | .vis e k => .vis e (fun x => .inr ⟨a, k x⟩)

instance : Monad (ITree E) where
  pure := ret
  bind := bind

/-- Perform a single event and return its answer. -/
def trigger (e : E A) : ITree E A where
  σ := Option A
  now := none
  step
    | none => .vis e some
    | some a => .ret a

/-- Loop: run `body i`; `.inl i'` goes around again (one silent step), `.inr r` exits with `r`. -/
def iter (body : I → ITree E (I ⊕ R)) (i : I) : ITree E R where
  σ := Σ i, (body i).σ
  now := ⟨i, (body i).now⟩
  step
    | ⟨i, s⟩ => match (body i).step s with
      | .ret (.inl i') => .tau ⟨i', (body i').now⟩
      | .ret (.inr r) => .ret r
      | .tau s' => .tau ⟨i, s'⟩
      | .vis e k => .vis e (fun x => ⟨i, k x⟩)

/-- `while`/`repeat` loops in `do` blocks, via `iter`. -/
instance (priority := high) instForInLoop : ForIn (ITree E) Lean.Loop Unit where
  forIn _ init f := iter (fun b => do
    match ← f () b with
    | .yield b => pure (.inl b)
    | .done b => pure (.inr b)) init

end ITree

/-- Sum of two event signatures: an event of `E ⊕ₑ F` is an event of either. -/
abbrev SumE (E F : Type → Type) : Type → Type := fun A => E A ⊕ F A
infixr:65 " ⊕ₑ " => SumE

/-- Memory events: handled by a heap model. -/
inductive MemEv : Type → Type where
  | deref (addr : Nat) : MemEv Nat
  | write (addr v : Nat) : MemEv Unit

/-- Host events: everything the outside world answers, including where `ref` allocates. -/
inductive HostEv : Type → Type where
  | print (v : Nat) : HostEv Unit
  | read : HostEv Nat
  | ref (v : Nat) : HostEv Nat

abbrev Ev := MemEv ⊕ₑ HostEv

def deref (a : Nat) : ITree Ev Nat := ITree.trigger (.inl (.deref a))
def write (a v : Nat) : ITree Ev Unit := ITree.trigger (.inl (.write a v))
def print (v : Nat) : ITree Ev Unit := ITree.trigger (.inr (.print v))
def read : ITree Ev Nat := ITree.trigger (.inr .read)
def ref (v : Nat) : ITree Ev Nat := ITree.trigger (.inr (.ref v))

/-- Variable values. -/
abbrev Vars := Nat → Nat
def Vars.set (vars : Vars) (x v : Nat) : Vars := fun y => if y = x then v else vars y
```

```lean
def eval (vars : Vars) : Expr → ITree Ev Nat
  | .lit n     => pure n
  | .var x     => pure (vars x)
  | .add a b   => do return (← eval vars a) + (← eval vars b)
  | .read      => read
  | .ref e     => do ref (← eval vars e)
  | .deref e   => do deref (← eval vars e)
  /- !hide -/
  | .sub a b   => do return (← eval vars a) - (← eval vars b)
  | .lt a b    => do return if (← eval vars a) < (← eval vars b) then 1 else 0

  /- !end hide -/
def exec (vars : Vars) : Stmt → ITree Ev Vars
  | .assign x e  => do return vars.set x (← eval vars e)
  | .print e     => do
      print (← eval vars e)
      return vars
  | .while c ss  => do
      let mut vars := vars
      while (← eval vars c) ≠ 0 do
        for s in ss do
          vars ← exec vars s
      return vars
  /- !hide -/
  | .store a e   => do write (← eval vars a) (← eval vars e); return vars
  | .ifThenElse c z nz => do
      let mut vars := vars
      if (← eval vars c) = 0 then
        for s in z do vars ← exec vars s
      else
        for s in nz do vars ← exec vars s
      return vars
  /- !end hide -/
```

```lean -show
end Interp
```

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
