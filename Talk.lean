module
public import VersoSlides

open VersoSlides

set_option verso.code.warnLineLength 500
set_option linter.unusedVariables false

#doc (Slides) "Representing Nonterminating Computation using iTrees" =>

# What do we need to verify Real-World Software?

* A Piece of Real-World Software
* {fragment (style := embolden)}[A Language Specification]
* A Behavioral Specification

# Real Languages are Messy

* Effects
```code rust
let config = fs::read_to_string("config.toml")?;
fs::write("config.bak", &config)?;
```

* Nontermination

```code rust
loop {
    let request = next_connection().await;
    respond(request).await;
}
```

* Nondeterminism and Undefined Behavior
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
  | alloc (size : Expr) | deref (addr : Expr)
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
p := alloc 1;
while 0 < n do
  store p (deref p + n);
  print (deref p);
  n := n - 1
```
:::


# Fueled Interpreter

```lean -show
abbrev Oracle := Nat → Nat   -- answer to the i-th `read`

inductive Event where | input (v : Nat) | output (v : Nat)
abbrev Trace := List Event

structure State where
  vars  : Nat → Option Nat := fun _ => none
  heap  : Nat → Option Nat := fun _ => none
  next  : Nat := 0
  reads : Nat := 0
  trace : Trace := []

def State.set (σ : State) (x v : Nat) : State :=
  { σ with vars := fun y => if y = x then some v else σ.vars y }
def State.input (σ : State) (v : Nat) : State :=
  { σ with reads := σ.reads + 1, trace := σ.trace ++ [.input v] }
def State.alloc (σ : State) (n : Nat) : State :=   -- bump-allocate `n` zeroed cells
  { σ with next := σ.next + n,
           heap := fun a => if σ.next ≤ a ∧ a < σ.next + n then some 0 else σ.heap a }
def State.allocated (σ : State) (a : Nat) : Bool := (σ.heap a).isSome
def State.store (σ : State) (a v : Nat) : State :=
  { σ with heap := fun b => if b = a then some v else σ.heap b }
def State.print (σ : State) (v : Nat) : State := { σ with trace := σ.trace ++ [.output v] }
-- on error, stop with the trace so far
def Except.orStop (r : Except ε (Nat × State)) (σ : State)
    (k : Nat → State → Trace × Option ε) : Trace × Option ε :=
  match r with | .ok (v, σ') => k v σ' | .error e => (σ.trace, some e)
```


:::class "big-code"
```lean
abbrev Fuel := Nat

inductive Error where | ub | outOfFuel | invalidVar

def eval (o : Oracle) (σ : State) : Expr → Except Error (Nat × State)
/- !hide -/
  | .lit n    => pure (n, σ)
  | .var x    => match σ.vars x with | some v => pure (v, σ) | none => throw .invalidVar
  | .add a b  => do let (a, σ) ← eval o σ a; let (b, σ) ← eval o σ b; pure (a + b, σ)
  | .sub a b  => do let (a, σ) ← eval o σ a; let (b, σ) ← eval o σ b; pure (a - b, σ)
  | .lt a b   => do let (a, σ) ← eval o σ a; let (b, σ) ← eval o σ b
                    pure (if a < b then 1 else 0, σ)
  | .deref a  => do
    let (a, σ) ← eval o σ a
    match σ.heap a with | some v => pure (v, σ) | none => throw .ub
  | .read     => let v := o σ.reads; pure (v, σ.input v)          -- pre-seeded
  | .alloc k  => do let (k, σ) ← eval o σ k; pure (σ.next, σ.alloc k)  -- we pick the block
/- !end hide -/
def exec (o : Oracle) (σ : State) : Fuel → Program → Trace × Option Error
  /- !hide -/
  -- TODO To Anyone reading: this snippet is vibecoded and I unfortunately didn't have more time to clean
  -- it up!
  | 0, _ :: _ => (σ.trace, some .outOfFuel)  -- diverged? or unlucky?
  | n+1, .while c s :: p => (eval o σ c).orStop σ fun v σ =>
      exec o σ n (if v ≠ 0 then s ++ .while c s :: p else p)
  | n+1, .assign x e :: p => (eval o σ e).orStop σ fun v σ => exec o (σ.set x v) n p
  | n+1, .store a v :: p => (eval o σ a).orStop σ fun a σ =>
      (eval o σ v).orStop σ fun v σ =>
      if σ.allocated a then exec o (σ.store a v) n p else (σ.trace, some .ub)
  | n+1, .print e :: p => (eval o σ e).orStop σ fun v σ => exec o (σ.print v) n p
  | n+1, .ifThenElse c z nz :: p => (eval o σ c).orStop σ fun v σ =>
      exec o σ n ((if v = 0 then z else nz) ++ p)
  | _,   []                   => (σ.trace, none)
  /- !end hide -/
```
:::

* Nontermination implicit (no fuel value that doesn't error)
* Nondeterminism and effect results require fixed implementations upfront

# Relational Big-Step

:::class "big-code"
```code toy
inductive BigStep : Stmt → State → State → Trace → Prop   -- ⟨s, σ⟩ ⇓ ⟨σ', t⟩
```
:::

:::class "big-code"
```code toy
⟨s₁, σ⟩ ⇓ ⟨σ₁, t₁⟩    ⟨s₂, σ₁⟩ ⇓ ⟨σ₂, t₂⟩         a ∈ ℕ    ⟨e, σ⟩ ⇓ n    ∀ i < n, σ.heap (a + i) = none
───────────────────────────────────────── (seq)   ───────────────────────────────────────────────────── (alloc)
     ⟨s₁ ; s₂, σ⟩ ⇓ ⟨σ₂, t₁ ++ t₂⟩                    ⟨x := alloc e, σ⟩ ⇓ ⟨σ[a..a+n ↦ₕ 0][x ↦ a], []⟩

                                        v ∈ ℕ
                         ─────────────────────────────────── (read)
                          ⟨x := read, σ⟩ ⇓ ⟨σ[x ↦ v], [in v]⟩
```
:::

* Nondeterminism & effects are "free" (e.g. `a` in `alloc`, `v` in `read`)
* Nontermination handled suboptimally
  * In Naive Big-Step: Stuck State (no derivation)
  * Fix 1: Add explicit nontermination judgments (duplicating rules)
  * Fix 2: Small-step-like relation

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

* Direct reasoning about nontermination
* Nondeterminism & effects are still "free"
* Requires explicitly modeling state transitions
* Resulting execution not immediately clear (⇒ bug-prone)
  * Lean 4 auto-implicits can obscure what is being quantified over
  * Accidental nondeterminism (several valid derivations for one state)
  * Unintended UB (via stuck states)


# Big Picture Comparison

:::table +colHeaders +rowHeaders +stripedRows +headerSep
*
  *
  * Fueled Interpreter
  * Big-Step Relation
  * Small-Step Relation
*
  * Executable?
  * ✅
  * ❌
  * ❌
*
  * Nontermination
  * 👎 Awkward quantification over `fuel`
  * 👎 Stuck State / UB / Duplicate Coinductive Rules
  * ✅ Infinite Step Sequence
*
  * Effects & Nondeterminism
  * 👎 Preset Responses / Concrete Model
  * ✅ Simple Derivation Pre-Condition
  * ✅ Simple Derivation Pre-Condition
*
  * Undefined Behavior (UB)
  * ✅ Explicit Error Kind
  * 👎 Stuck State
  * 👎 Stuck State
  
:::


:::fragment fadeUp (index := 1)
*What does our Ideal Version look like?*

* Executable
* Trivially Nonterminating
* Abstract / Modular Effects
* UB Explicit
:::

# Interaction Trees (iTrees)

```html
<img class="itree-diagram" src="itree-state.svg" alt="State diagram of the example program">
```

# Interaction Trees (iTrees) (2)

```html
<img class="itree-diagram" src="itree-tree.svg" alt="The example program unfolded into an iTree">
```

Every answer picks a branch and the loop unrolls once per iteration: a finite program, an infinitely branching tree.

# iTree Based Interpreter

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

/-- A recursive call with argument `I`, answered with `O`. -/
inductive Call (I O : Type) : Type → Type where
  | call (i : I) : Call I O O

/-- Rename events: same states, every `vis e` becomes `vis (f e)`. -/
def ITree.mapE (f : ∀ {A}, E A → F A) (t : ITree E R) : ITree F R where
  σ := t.σ
  now := t.now
  step s := match t.step s with
    | .ret r => .ret r
    | .tau s' => .tau s'
    | .vis e k => .vis (f e) k

instance : MonadLift (ITree E) (ITree (D ⊕ₑ E)) where
  monadLift := ITree.mapE .inr

/-- Recursion: `body i` computes the answer at `i` and may emit `call j`. The state is the running
frame plus a stack of suspended callers, each waiting for an `O`. Calls and returns are silent. -/
def ITree.recCall (body : I → ITree (Call I O ⊕ₑ E) O) (i : I) : ITree E O where
  σ := (Σ i, (body i).σ) × List (Σ i, O → (body i).σ)
  now := (⟨i, (body i).now⟩, [])
  step
    | (⟨i, s⟩, stack) => match (body i).step s, stack with
      | .ret o, [] => .ret o
      | .ret o, ⟨i', k⟩ :: stack => .tau (⟨i', k o⟩, stack)
      | .tau s', stack => .tau (⟨i, s'⟩, stack)
      | .vis (.inl (.call j)) k, stack => .tau (⟨j, (body j).now⟩, ⟨i, k⟩ :: stack)
      | .vis (.inr e) k, stack => .vis e (fun x => (⟨i, k x⟩, stack))

/-- Fixpoint combinator: `f` receives the recursive function as a closure. Calling the closure
emits a `call` event, which `recCall` turns into a pushed stack frame (cf. `rec_fix` in Coq ITrees). -/
def ITree.fix (f : (I → ITree (Call I O ⊕ₑ E) O) → I → ITree (Call I O ⊕ₑ E) O) : I → ITree E O :=
  ITree.recCall (f fun i => ITree.trigger (.inl (.call i)))

/-- Memory events: handled by a heap model. -/
inductive MemEv : Type → Type where
  | deref (addr : Nat) : MemEv Nat
  | write (addr v : Nat) : MemEv Unit

/-- Host events: everything the outside world answers, including where `alloc` places a block. -/
inductive HostEv : Type → Type where
  | print (v : Nat) : HostEv Unit
  | read : HostEv Nat
  | alloc (size : Nat) : HostEv Nat

abbrev Ev := MemEv ⊕ₑ HostEv

def deref (a : Nat) : ITree Ev Nat := ITree.trigger (.inl (.deref a))
def write (a v : Nat) : ITree Ev Unit := ITree.trigger (.inl (.write a v))
def print (v : Nat) : ITree Ev Unit := ITree.trigger (.inr (.print v))
def read : ITree Ev Nat := ITree.trigger (.inr .read)
def alloc (n : Nat) : ITree Ev Nat := ITree.trigger (.inr (.alloc n))

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
  | .alloc e   => do alloc (← eval vars e)
  | .deref e   => do deref (← eval vars e)
  -- | .sub a b => ... | .lt a b => ...
  /- !hide -/
  | .sub a b   => do return (← eval vars a) - (← eval vars b)
  | .lt a b    => do return if (← eval vars a) < (← eval vars b) then 1 else 0

  /- !end hide -/
def exec : Vars × Stmt → ITree Ev Vars := ITree.fix fun exec (vars, s) => match s with
  | .assign x e  => do return vars.set x (← eval vars e)
  | .print e     => do print (← eval vars e); return vars
  | .while c ss  => do
      let mut vars := vars
      while (← eval vars c) ≠ 0 do
        for s in ss do
          vars ← exec (vars, s)
      return vars
  | .store a e   => do write (← eval vars a) (← eval vars e); return vars
  | .ifThenElse c z nz => do
      let branch := if (← eval vars c) = 0 then z else nz
      let mut vars := vars
      for s in branch do
        vars ← exec (vars, s)
      return vars
  /- !hide -/
  /- !end hide -/
```

```lean -show
end Interp
```

# What iTrees Give You

* Nontermination (Unbounded Loops & Recursion)
* Quasi-Executable with Modular Effects (executable shape fixed, only effects need concrete definitions)
* Explicit UB (Explicit Kind / Non-resumable Effect)

# How iTrees Work

```lean
/---- iTrees are just fancy State Machines ----/

inductive Step (Effect : Type → Type) (Res State : Type) : Type 1 where
  | ret (r : Res)
  | tau (next : State)
  | vis {A : Type} (e : Effect A) (k : A → State)

structure ITree (E : Type → Type) (R : Type) : Type 1 where
  σ : Type
  now : σ
  step : σ → Step E R σ

/---- iTrees as Monads ----/

def ITree.pure (r : R) : ITree E R := ⟨Unit, (), fun () => .ret r⟩

def ITree.bind (t : ITree E A) (g : A → ITree E B) : ITree E B where
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
```

# Recap

It's all about the Specification

- Bugs in the Specification undermine the Soundness of your Verification
- With AI *you are the bottleneck* ⇒ anything that makes critical code less painful to audit is a win
- Typical language formalization approaches are suboptimal
- iTrees are great

