/-
Prototype: big-step semantics whose rules are written as inference rules,

    | seq :
        ⟨s₁, σ⟩ ⇓ σ₁    ⟨s₂, σ₁⟩ ⇓ σ₂
        ─────────────────────────────
        ⟨s₁ ; s₂, σ⟩ ⇓ σ₂

Two judgements share the arrow:
  `⟨e, σ⟩ ⇓ ⟨v, σ'⟩`   expressions (relation `Eval`), value and final state
  `⟨s, σ⟩ ⇓ σ'`        statements  (relation `BigStep`)

The `rules` command expands to an ordinary `inductive`; premises become
arrows and free variables are auto-bound, as in a hand-written constructor.

Check with `lake env lean Proto/BigStep.lean`.
-/

namespace Proto

/-! ## Language -/

abbrev Var := String

inductive Expr where
  | lit   : Nat → Expr
  | var   : Var → Expr
  | add   : Expr → Expr → Expr
  | sub   : Expr → Expr → Expr
  | lt    : Expr → Expr → Expr
  | load  : Expr → Expr
  | alloc : Expr → Expr
  deriving Repr

inductive Stmt where
  | skip   : Stmt
  | assign : Var → Expr → Stmt
  | letIn  : Var → Expr → Stmt → Stmt
  | seq    : Stmt → Stmt → Stmt
  | ite    : Expr → Stmt → Stmt → Stmt
  | while  : Expr → Stmt → Stmt
  | store  : Expr → Expr → Stmt
  deriving Repr

structure State where
  vars : Var → Nat
  heap  : Nat → Option Nat

instance : EmptyCollection State := ⟨⟨fun _ => 0, fun _ => none⟩⟩

def State.set (σ : State) (x : Var) (v : Nat) : State :=
  { σ with vars := fun y => if y = x then v else σ.vars y }

def State.write (σ : State) (ℓ v : Nat) : State :=
  { σ with heap := fun a => if a = ℓ then some v else σ.heap a }

-- `noWs` + `:max` so these bind as tightly as `xs[i]`.
syntax:max term noWs "[" term " ↦ " term "]" : term
syntax:max term noWs "[" term " ↦ₕ " term "]" : term
macro_rules
  | `($σ[$x ↦ $v]) => `(State.set $σ $x $v)
  | `($σ[$ℓ ↦ₕ $v]) => `(State.write $σ $ℓ $v)

/-! ## Concrete syntax for programs

Identifiers are Lean terms (metavariables in rules, defs in examples);
string literals are program variables. `lit n` / `var x` embed a Lean
`Nat` / `Var` metavariable. -/

-- `both`: a leading identifier may also be read as `lit`/`var`/`alloc`,
-- which stay ordinary identifiers everywhere else.
declare_syntax_cat ex (behavior := both)
declare_syntax_cat stmt

syntax:max num : ex
syntax:max str : ex
syntax:max ident : ex
syntax:max &"lit " term:max : ex
syntax:max &"var " term:max : ex
syntax:65 ex:65 " + " ex:66 : ex
syntax:65 ex:65 " - " ex:66 : ex
syntax:50 ex:51 " < " ex:51 : ex
syntax:max "!" ex:max : ex
syntax:max &"alloc " ex:max : ex
syntax:max "(" ex ")" : ex

syntax ident : stmt
syntax:20 (ident <|> str) " := " ex : stmt
syntax:20 "*" ex:max " := " ex : stmt
syntax:20 "let " (ident <|> str) " := " ex " in " stmt:20 : stmt
syntax:20 "if " ex " then " stmt:20 " else " stmt:20 : stmt
syntax:20 "while " ex " do " stmt:20 : stmt
syntax:10 stmt:11 " ; " stmt:10 : stmt
syntax "(" stmt ")" : stmt

syntax "[ex| " ex "]" : term
syntax "[stmt| " stmt "]" : term

macro_rules
  | `([ex| $n:num]) => `(Expr.lit $n)
  | `([ex| $s:str]) => `(Expr.var $s)
  | `([ex| $x:ident]) => `($x)
  | `([ex| lit $n]) => `(Expr.lit $n)
  | `([ex| var $x]) => `(Expr.var $x)
  | `([ex| $a + $b]) => `(Expr.add [ex| $a] [ex| $b])
  | `([ex| $a - $b]) => `(Expr.sub [ex| $a] [ex| $b])
  | `([ex| $a < $b]) => `(Expr.lt [ex| $a] [ex| $b])
  | `([ex| !$a]) => `(Expr.load [ex| $a])
  | `([ex| alloc $a]) => `(Expr.alloc [ex| $a])
  | `([ex| ($a)]) => `([ex| $a])

macro_rules
  | `([stmt| $s:ident]) =>
    -- `skip` is not a keyword (it would clash with the rule name `| skip :`).
    if s.getId == `skip then `(Stmt.skip) else `($s)
  | `([stmt| $x:ident := $e]) => `(Stmt.assign $x [ex| $e])
  | `([stmt| $x:str := $e]) => `(Stmt.assign $x [ex| $e])
  | `([stmt| *$a := $e]) => `(Stmt.store [ex| $a] [ex| $e])
  | `([stmt| let $x:ident := $e in $s]) => `(Stmt.letIn $x [ex| $e] [stmt| $s])
  | `([stmt| let $x:str := $e in $s]) => `(Stmt.letIn $x [ex| $e] [stmt| $s])
  | `([stmt| if $c then $s₁ else $s₂]) => `(Stmt.ite [ex| $c] [stmt| $s₁] [stmt| $s₂])
  | `([stmt| while $c do $s]) => `(Stmt.while [ex| $c] [stmt| $s])
  | `([stmt| $s₁ ; $s₂]) => `(Stmt.seq [stmt| $s₁] [stmt| $s₂])
  | `([stmt| ($s)]) => `([stmt| $s])

/-! ## Judgements and the `rules` command -/

/-- The state after a statement. A separate category (not `term`) so that it
cannot start with `⟨`: that is what tells `⟨s, σ⟩ ⇓ σ'` apart from
`⟨e, σ⟩ ⇓ ⟨v, σ'⟩` when `s`/`e` is a bare identifier, and it also stops the
state from swallowing the next premise as a function argument. -/
declare_syntax_cat state
syntax ident : state
syntax "(" term ")" : state
syntax:max state noWs "[" term " ↦ " term "]" : state
syntax:max state noWs "[" term " ↦ₕ " term "]" : state

syntax "[state| " state "]" : term
macro_rules
  | `([state| $x:ident]) => `($x)
  | `([state| ($t)]) => `($t)
  | `([state| $σ[$x ↦ $v]]) => `(State.set [state| $σ] $x $v)
  | `([state| $σ[$ℓ ↦ₕ $v]]) => `(State.write [state| $σ] $ℓ $v)

declare_syntax_cat judgement
syntax "⟨" ex ", " term "⟩" " ⇓ " "⟨" term ", " term "⟩" : judgement
syntax "⟨" stmt ", " term "⟩" " ⇓ " state : judgement
/-- A side condition, any Lean proposition. -/
syntax "(" term ")" : judgement

/-- A judgement as a proposition: expression judgements mean `Eval`,
statement judgements mean `BigStep`. -/
syntax "⟦" judgement "⟧" : term
macro_rules
  | `(⟦⟨$e:ex, $σ⟩ ⇓ ⟨$v, $σ'⟩⟧) => `($(Lean.mkIdent `Eval) [ex| $e] $σ $v $σ')
  | `(⟦⟨$s:stmt, $σ⟩ ⇓ $σ':state⟧) => `($(Lean.mkIdent `BigStep) [stmt| $s] $σ [state| $σ'])
  | `(⟦($p)⟧) => `($p)

syntax ruleLine := ("─" <|> "-")+
syntax inferenceRule := "| " ident " :" judgement* ruleLine judgement
syntax "rules " ident " : " term " where" inferenceRule* : command

macro_rules
  | `(rules $R : $ty where $rs:inferenceRule*) => do
    let ctors ← rs.mapM fun r => match r with
      | `(inferenceRule| | $n : $ps* $_:ruleLine $c) => do
        let mut t ← `(⟦$c⟧)
        for p in ps.reverse do
          t ← `(⟦$p⟧ → $t)
        return (n, t)
      | _ => Lean.Macro.throwUnsupported
    let (ns, ts) := ctors.unzip
    `(inductive $R : $ty where $[| $ns:ident : $ts]*)

/-! ## Big-step semantics, as inference rules -/


rules Eval : Expr → State → Nat → State → Prop where
  | lit :
      ─────────────────────
      ⟨lit n, σ⟩ ⇓ ⟨n, σ⟩

  | var :
      ──────────────────────────────
      ⟨var x, σ⟩ ⇓ ⟨σ.vars x, σ⟩

  | add :
      ⟨a, σ⟩ ⇓ ⟨v₁, σ₁⟩    ⟨b, σ₁⟩ ⇓ ⟨v₂, σ₂⟩
      ──────────────────────────────────────
      ⟨a + b, σ⟩ ⇓ ⟨v₁ + v₂, σ₂⟩

  | sub :
      ⟨a, σ⟩ ⇓ ⟨v₁, σ₁⟩    ⟨b, σ₁⟩ ⇓ ⟨v₂, σ₂⟩
      ──────────────────────────────────────
      ⟨a - b, σ⟩ ⇓ ⟨v₁ - v₂, σ₂⟩

  | lt :
      ⟨a, σ⟩ ⇓ ⟨v₁, σ₁⟩    ⟨b, σ₁⟩ ⇓ ⟨v₂, σ₂⟩
      ──────────────────────────────────────────────
      ⟨a < b, σ⟩ ⇓ ⟨if v₁ < v₂ then 1 else 0, σ₂⟩

  | load :
      ⟨a, σ⟩ ⇓ ⟨ℓ, σ₁⟩    (σ₁.heap ℓ = some v)
      ──────────────────────────────────────
      ⟨!a, σ⟩ ⇓ ⟨v, σ₁⟩

  | alloc :
      ⟨e, σ⟩ ⇓ ⟨v, σ₁⟩    (σ₁.heap ℓ = none)
      ──────────────────────────────────────
      ⟨alloc e, σ⟩ ⇓ ⟨ℓ, σ₁[ℓ ↦ₕ v]⟩

rules BigStep : Stmt → State → State → Prop where
  | skip :
      ──────────────────
      ⟨skip, σ⟩ ⇓ σ

  | assign :
      ⟨e, σ⟩ ⇓ ⟨v, σ₁⟩
      ─────────────────────────
      ⟨x := e, σ⟩ ⇓ σ₁[x ↦ v]

  | letIn :
      ⟨e, σ⟩ ⇓ ⟨v, σ₁⟩    ⟨s, σ₁[x ↦ v]⟩ ⇓ σ₂
      ─────────────────────────────────────────
      ⟨let x := e in s, σ⟩ ⇓ σ₂[x ↦ σ.vars x]

  | seq :
      ⟨s₁, σ⟩ ⇓ σ₁    ⟨s₂, σ₁⟩ ⇓ σ₂
      ─────────────────────────────
      ⟨s₁ ; s₂, σ⟩ ⇓ σ₂

  | ifTrue :
      ⟨e, σ⟩ ⇓ ⟨v, σ₁⟩    (v ≠ 0)    ⟨s₁, σ₁⟩ ⇓ σ₂
      ────────────────────────────────────────────
      ⟨if e then s₁ else s₂, σ⟩ ⇓ σ₂

  | ifFalse :
      ⟨e, σ⟩ ⇓ ⟨v, σ₁⟩    (v = 0)    ⟨s₂, σ₁⟩ ⇓ σ₂
      ────────────────────────────────────────────
      ⟨if e then s₁ else s₂, σ⟩ ⇓ σ₂

  | whileFalse :
      ⟨e, σ⟩ ⇓ ⟨v, σ₁⟩    (v = 0)
      ──────────────────────────
      ⟨while e do s, σ⟩ ⇓ σ₁

  | whileTrue :
      ⟨e, σ⟩ ⇓ ⟨v, σ₁⟩    (v ≠ 0)
      ⟨s, σ₁⟩ ⇓ σ₂    ⟨while e do s, σ₂⟩ ⇓ σ₃
      ───────────────────────────────────────
      ⟨while e do s, σ⟩ ⇓ σ₃

  | store :
      ⟨a, σ⟩ ⇓ ⟨ℓ, σ₁⟩    ⟨e, σ₁⟩ ⇓ ⟨v, σ₂⟩    (σ₂.heap ℓ ≠ none)
      ──────────────────────────────────────────────────────
      ⟨*a := e, σ⟩ ⇓ σ₂[ℓ ↦ₕ v]

#print Eval
#print BigStep

/-! ## The same relations, as plain `inductive`s -/

namespace Plain

inductive Eval : Expr → State → Nat → State → Prop where
  | lit : Eval (.lit n) σ n σ
  | var : Eval (.var x) σ (σ.vars x) σ
  | add : Eval a σ v₁ σ₁ → Eval b σ₁ v₂ σ₂ → Eval (.add a b) σ (v₁ + v₂) σ₂
  | sub : Eval a σ v₁ σ₁ → Eval b σ₁ v₂ σ₂ → Eval (.sub a b) σ (v₁ - v₂) σ₂
  | lt :
      Eval a σ v₁ σ₁ → Eval b σ₁ v₂ σ₂ →
      Eval (.lt a b) σ (if v₁ < v₂ then 1 else 0) σ₂
  | load : Eval a σ ℓ σ₁ → σ₁.heap ℓ = some v → Eval (.load a) σ v σ₁
  | alloc : Eval e σ v σ₁ → σ₁.heap ℓ = none → Eval (.alloc e) σ ℓ (σ₁.write ℓ v)

inductive BigStep : Stmt → State → State → Prop where
  | skip : BigStep .skip σ σ
  | assign : Eval e σ v σ₁ → BigStep (.assign x e) σ (σ₁.set x v)
  | letIn :
      Eval e σ v σ₁ → BigStep s (σ₁.set x v) σ₂ →
      BigStep (.letIn x e s) σ (σ₂.set x (σ.vars x))
  | seq : BigStep s₁ σ σ₁ → BigStep s₂ σ₁ σ₂ → BigStep (.seq s₁ s₂) σ σ₂
  | ifTrue : Eval e σ v σ₁ → v ≠ 0 → BigStep s₁ σ₁ σ₂ → BigStep (.ite e s₁ s₂) σ σ₂
  | ifFalse : Eval e σ v σ₁ → v = 0 → BigStep s₂ σ₁ σ₂ → BigStep (.ite e s₁ s₂) σ σ₂
  | whileFalse : Eval e σ v σ₁ → v = 0 → BigStep (.while e s) σ σ₁
  | whileTrue :
      Eval e σ v σ₁ → v ≠ 0 → BigStep s σ₁ σ₂ → BigStep (.while e s) σ₂ σ₃ →
      BigStep (.while e s) σ σ₃
  | store :
      Eval a σ ℓ σ₁ → Eval e σ₁ v σ₂ → σ₂.heap ℓ ≠ none →
      BigStep (.store a e) σ (σ₂.write ℓ v)

end Plain

theorem Eval.iff_plain : Eval e σ v σ' ↔ Plain.Eval e σ v σ' := by
  constructor <;> intro h <;> induction h <;> constructor <;> assumption

local macro "premise" : tactic =>
  `(tactic| first | assumption | exact Eval.iff_plain.1 ‹_› | exact Eval.iff_plain.2 ‹_›)

theorem BigStep.iff_plain : BigStep s σ σ' ↔ Plain.BigStep s σ σ' := by
  constructor <;> intro h <;> induction h <;> first
    | (apply Plain.BigStep.skip) | (apply BigStep.skip)
    | (apply Plain.BigStep.assign <;> premise) | (apply BigStep.assign <;> premise)
    | (apply Plain.BigStep.letIn <;> premise) | (apply BigStep.letIn <;> premise)
    | (apply Plain.BigStep.seq <;> premise) | (apply BigStep.seq <;> premise)
    | (apply Plain.BigStep.ifTrue <;> premise) | (apply BigStep.ifTrue <;> premise)
    | (apply Plain.BigStep.ifFalse <;> premise) | (apply BigStep.ifFalse <;> premise)
    | (apply Plain.BigStep.whileFalse <;> premise) | (apply BigStep.whileFalse <;> premise)
    | (apply Plain.BigStep.whileTrue <;> premise) | (apply BigStep.whileTrue <;> premise)
    | (apply Plain.BigStep.store <;> premise) | (apply BigStep.store <;> premise)

/-! ## Examples -/

/-- Closes a side condition; fails rather than leaving a goal behind. -/
local macro "side" : tactic =>
  `(tactic| first | decide | (simp [State.set, State.write, EmptyCollection.emptyCollection]; done))

/-- Derives an expression judgement for an `alloc`-free expression. -/
syntax "eval_expr" : tactic
macro_rules
  | `(tactic| eval_expr) => `(tactic| first
    | apply Eval.lit | apply Eval.var
    | (apply Eval.add <;> eval_expr) | (apply Eval.sub <;> eval_expr)
    | (apply Eval.lt <;> eval_expr)
    | (apply Eval.load
       · eval_expr
       first | exact rfl | (simp [State.set, State.write]; rfl)))

/-- Runs an `alloc`-free program: the guard is evaluated, then the branch
whose side condition holds is taken. -/
syntax "run_bigstep" : tactic
macro_rules
  | `(tactic| run_bigstep) => `(tactic| first
    | (apply BigStep.whileFalse
       · eval_expr
       side)
    | (apply BigStep.whileTrue
       · eval_expr
       · side
       · run_bigstep
       run_bigstep)
    | (apply BigStep.ifTrue
       · eval_expr
       · side
       run_bigstep)
    | (apply BigStep.ifFalse
       · eval_expr
       · side
       run_bigstep)
    | apply BigStep.skip
    | (apply BigStep.seq
       · run_bigstep
       run_bigstep)
    | (apply BigStep.assign; eval_expr)
    | (apply BigStep.letIn
       · eval_expr
       run_bigstep)
    | (apply BigStep.store
       · eval_expr
       · eval_expr
       side))

def countdown := [stmt| "n" := 3 ; while 0 < "n" do "n" := "n" - 1]

example : ∃ σ', ⟦⟨countdown, ∅⟩ ⇓ σ'⟧ ∧ σ'.vars "n" = 0 := by
  apply Exists.intro
  constructor
  · run_bigstep
  · rfl

/-- `let` restores the shadowed variable. -/
example : ∃ σ', ⟦⟨"x" := 1 ; let "x" := 5 in "y" := "x", ∅⟩ ⇓ σ'⟧
    ∧ σ'.vars "x" = 1 ∧ σ'.vars "y" = 5 := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · run_bigstep
  all_goals rfl

/-- An expression judgement: allocating in the empty heap may return any address. -/
example (ℓ : Nat) : ⟦⟨alloc 7, ∅⟩ ⇓ ⟨ℓ, (∅ : State)[ℓ ↦ₕ 7]⟩⟧ :=
  Eval.alloc Eval.lit rfl

def bump := [stmt| "p" := alloc 7 ; *"p" := !"p" + 1 ; "r" := !"p"]

/-- `bump` runs to completion whichever address `ℓ` the allocation picks. -/
theorem bump_runs (ℓ : Nat) : ∃ σ', ⟦⟨bump, ∅⟩ ⇓ σ'⟧ := by
  apply Exists.intro
  apply BigStep.seq
  · exact BigStep.assign (Eval.alloc (ℓ := ℓ) Eval.lit rfl)
  · run_bigstep

/-- Allocation is nondeterministic: two runs end with `p` at different addresses. -/
example : ∃ σ₁ σ₂, ⟦⟨bump, ∅⟩ ⇓ σ₁⟧ ∧ ⟦⟨bump, ∅⟩ ⇓ σ₂⟧ ∧ σ₁.vars "p" ≠ σ₂.vars "p" := by
  apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · apply BigStep.seq
    · exact BigStep.assign (Eval.alloc (ℓ := 0) Eval.lit rfl)
    · run_bigstep
  · apply BigStep.seq
    · exact BigStep.assign (Eval.alloc (ℓ := 1) Eval.lit rfl)
    · run_bigstep
  · side

/-- Every run, whatever address it picks, reads back `8`. -/
theorem bump_reads_8 (h : ⟦⟨bump, ∅⟩ ⇓ σ'⟧) : σ'.vars "r" = 8 := by
  cases h with | seq h₁ h =>
  cases h with | seq h₂ h₃ =>
  cases h₁ with | assign he =>
  cases he with | alloc he₁ _ =>
  cases he₁
  cases h₂ with | store ha he₂ _ =>
  cases ha
  cases he₂ with | add hl hr =>
  cases hr
  cases hl with | load hv hs =>
  cases hv
  cases h₃ with | assign he₃ =>
  cases he₃ with | load hv' hs' =>
  cases hv'
  simp_all [State.set, State.write]
  omega

/-! ## A general lemma: allocated cells stay allocated -/

theorem Eval.heap_mono (h : ⟦⟨e, σ⟩ ⇓ ⟨v, σ'⟩⟧) (ha : σ.heap a ≠ none) :
    σ'.heap a ≠ none := by
  induction h with
  | alloc _ _ ih => simp only [State.write]; split <;> simp_all
  | _ => simp_all

theorem BigStep.heap_mono (h : ⟦⟨s, σ⟩ ⇓ σ'⟧) (ha : σ.heap a ≠ none) :
    σ'.heap a ≠ none := by
  induction h with
  | skip => exact ha
  | assign he => exact he.heap_mono ha
  | letIn he _ ih => exact ih (he.heap_mono ha)
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ ha)
  | ifTrue he _ _ ih | ifFalse he _ _ ih => exact ih (he.heap_mono ha)
  | whileFalse he _ => exact he.heap_mono ha
  | whileTrue he _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ (he.heap_mono ha))
  | store h₁ h₂ _ =>
    have := h₂.heap_mono (h₁.heap_mono ha)
    simp only [State.write]; split <;> simp_all

end Proto
