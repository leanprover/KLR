/-
# 💻 Dataflow Solver 🥳

This is a file, originally authored by Julia, performing semilattice-join fixpoint
search based dataflow analysis!
In other words, a graph is the carrier for a datum of type `β` at each node.
These data are expected to follow the constraint `τ(β) ≤ β'`, where `τ : β → β` is a
node-specific "transition function", `β'` is any succesor of `β` in the graph, and `≤` is
the semitlattice order.
A "solution" is a set of data over the graph carrier satisfying these constraints.
This file exists to compute such solutions.

note: this file considers only _partial_ correctness. _total_ correctness, i.e. proving
(conditional) termination, has been considered out of scope. In practice, a 'fuel' parameter
to the search loop in `DataflowProblem.solve_to_depth` can be easily set above theoretical
upper bonds on search duration. 😊

## Workflow 🫡

To instantiate the solver in general, for graphs whose nodes are indexed by a type `α`, and
whose data are drawn from a type `β`, begin by providing an instance of `DataflowProblem α β`.

```class DataflowProblem (α β : Type) ...```

(Note... this involves instantiating several typeclasses, including the most heavyeight:
  `NodeMap α` - which provides the type `⟦α, β⟧` of maps from nodes `α` to data `β`)
(The Class NodeProp α, which provides the structure type `Node α`, fixes
`node_prop : α → Prop` that idenitifes the subset of the type `α` corresponding to
nodes in the graph.)

Once a `dataflowProblem : DataflowProblem` is created, call `dataflowProblem.solve`.
```
def DataflowProblem.solve {α β : Type} ...
  (DP : DataflowProblem α β)
  : Option ((ν : ⟦α, β⟧) ×' I' ν)
```
This will perform a fuel-based terminating fixpoint search for a dataflow solution ✌️.
if one is found, then `dataflowProblem.solve = some ⟨ν, ν_sound⟩`, where `ν` is
the solution and `ν_sound : Prop` proves its a solution (see `def E` through
 `def I'`) for structure of solution soundness theorems 🦾.

## Finite Graph Workflow #️⃣🌎🔢

When `Node α` is a finite type of size `n`, `⟦α, β] = Vector β n` suffices. This
choice fixes a large amount of the "boilerplate" in `DataflowProblem`. The class
`FiniteSolverInput β` consists primarily of three fields:
```
structure FiniteSolverInput (β : Type) ...
  num_nodes : ℕ
  edges : ℕ → ℕ → Bool
  transitions : ℕ → β → β
  ...
```
`num_nodes` is the number of nodes in the graph. `edges` and `transitions` operate on
the on node numbers (`Nat`s less than `num_nodes`). `edges` is a boolean relation
indicating the edge relation, and `transitions` provides the transition functions
`β → β` per node. Finally, lightweight soundness conditions on these entries
(`transitions_sound` `le_sound` `le_supl` `le_supr`) must be proved.

Once a `FiniteSolverInput` instance is defined, it can be passed to the function
 `FiniteDataflowProblem` to create a corresponding `DataflowProblem` instance:

```
def FiniteDataflowProblem {β : Type} ...
  (FSI : FiniteSolverInput β)
  : DataflowProblem ℕ β
```

`DataflowProblem.solve` may then be called on this instance.

## Concrete example : constant propagation


## Code by `Section`

`Section Basics`- defines basic `Node`, `NodeProp`, and `NodeMap `definitions.
  Culminates in `DataflowProblem` definition relying on `NodeMap`s.

`Section DataflowProblemSolver` - defines computations and logic on `DataflowProblem`s,
  culminating in `DataflowProblem.solve` definition that provides a solution
  to dataflow problems.

`Section FiniteDataflowProblemSolver` - simplies the process of constructing
  `DataflowProblem`s by proviing the `FiniteSolverInput` class that uses
  `ℕ` indexing for nodes, and can be transformed by `FiniteDataflowProblem`
  to a `DataflowProblem`.

`Section InnerMapImpl` - description TBD

`Section ConcreteMapImpl` - description TBD
-/
import Lean.Data.RBMap

abbrev ℕ := Nat

/-
  The section `Basics` provides the basic typeclasses, structures, and
  notations needed to define `DataflowProblem` - including maps,
  map operations, and operations like `≤` and `⊔` -/
section Basics

  /-
    An instance `_ : NodeProp α` fixes a `node_prop : α → Prop` that
    defines the set of nodes (note `Set α := α → Prop`) in the carrier
    graph.
  -/
  class NodeProp (α : Type) where
    node_prop : α → Prop

  /-
    With a `NodeProp α` in scope, `Node α` is the subtype of `a : α` that
    can prove `node_prop a` (i.e., are indeed nodes in the carrier graph)
  -/
  structure Node (α : Type) [NP : NodeProp α] where
    data : α
    sound : NP.node_prop data

  instance {α} [TSA : ToString α] [NodeProp α]: ToString (Node α) where
    toString := (TSA.toString ·.data)

  instance {α} [BEq α] [NodeProp α]: BEq (Node α) where
    beq a₀ a₁ := a₀.data == a₁.data

  /-
    In the context of a set of nodes `Node α` fixed by a `NodeProp α`, an
    instance of `NodeMap α` is a constructor for map objects whose domain
    is the nodes of the carrier graph and whose codomain is a datatype `β`.

    Several utilities, as well as soundness theorems on them including
    two induction principles, are required as well.
  -/
  class NodeMap (α : Type) extends NodeProp α where
    μ (β : Type) : Type -- type of maps
    const {β} : β → μ β -- empty instance
    of_func {β} : (Node α → β) → μ β --instance from func
    get {β} : (μ β) → Node α → β
    fold {β γ} : (μ β) → ((Node α) → γ → γ) → γ → γ
    app_unary {β γ} : (μ β) → (β → γ) → (μ γ)
    app_binary {β₀ β₁ γ} : (μ β₀) → (μ β₁) → (β₀ → β₁ → γ) → (μ γ)

    of_const_get {β} (b : β) a : get (const b) a = b
    of_func_get {β} (f : Node α → β) a : get (of_func f) a = f a
    of_map_get {β γ} μ (f : β → γ) a : get (app_unary μ f) a = f (get μ a)
    of_app_binary_get {β₀ β₁ γ} μ₀ μ₁ (f : β₀ → β₁ → γ) a
      : get (app_binary μ₀ μ₁ f) a = f (get μ₀ a) (get μ₁ a)

    fold_ind {β γ} {ν : μ β} {γ₀ : γ} {acc : (Node α) → γ → γ} :
      (P : γ → Prop) →
      (P γ₀) →
      (∀ a γ, P γ → P (acc a γ)) →
      P (fold ν acc γ₀)

    fold_strong_ind {β γ} {ν : μ β} {γ₀ : γ} {acc : Node α → γ → γ} :
      (P : Node α → γ → Prop) →
      (∀ a γ₀, P a (acc a γ₀)) →
      (∀ a γ₀ b, P a γ₀ → P a (acc b γ₀)) →
      (∀ a, P a (fold ν acc γ₀))

  -- An instance `HasBot α` fixes a bottom element (`⊥`) of type `α`.
  class HasBot (α : Type) where
    bot : α

  notation "⊥" => HasBot.bot

  notation μ "fold⟪" st "," acc "⟫" => NodeMap.fold μ acc st

  instance {α β : Type} [ToString α] [ToString β] [NM:NodeMap α]
    : ToString (NM.μ β) where
    toString μ := NM.fold μ (fun nd str =>
      str ++ "{" ++ (toString nd.data) ++ ":"
                  ++ (toString (NM.get μ nd)) ++ "}\n") ""


  notation "⟦" α  "," β "⟧" => NodeMap.μ α β

  infix:90 "◃" => NodeMap.get

  notation "⟪↦" b "⟫"=> NodeMap.const b

  notation μ "map⟪" f "⟫" => NodeMap.app_unary μ f

  notation "of_func⟪" f "⟫" => NodeMap.of_func f

  notation "map2⟪" μ₀ "," μ₁ "," f "⟫" => NodeMap.app_binary μ₀ μ₁ f

  instance {α β : Type} [NodeMap α] [LE β] : LE ⟦α, β⟧ where
    le μ₀ μ₁ := (a : Node α) → (μ₀◃a ≤ μ₁◃a)

  instance {α β : Type} [NodeMap α] [Max β] : Max ⟦α, β⟧ where
    max μ₀ μ₁ := map2⟪μ₀, μ₁, (Max.max · ·)⟫

  infix:100 "⊔" => Max.max

  def NodeMap.instBEq {α β : Type} [NodeMap α] [BEq β] : BEq ⟦α, β⟧ := {
    beq μ₀ μ₁ := μ₀ fold⟪true, (fun a prev => prev ∧ (μ₀◃a == μ₁◃a))⟫
  }

  instance {α β : Type} [NodeMap α] [BEq β] : BEq ⟦α, β⟧ := NodeMap.instBEq

  theorem NodeMap.beq_ext {α β : Type} [BEq β] [NodeMap α] (μ₀ μ₁ : ⟦α, β⟧)
    : μ₀ == μ₁ ↔ (∀ a, μ₀◃a == μ₁◃a) := by {
      constructor
      {
        intro hμeq a
        cases heq : (μ₀◃a == μ₁◃a)
        {
          have hμneq : (μ₀ == μ₁) = false := by {
            unfold BEq.beq instBEqμ instBEq
            simp
            let P := fun a b ↦ (μ₀◃a == μ₁◃a) = false → b = false
            apply (NodeMap.fold_strong_ind P)<;>try unfold P<;>try simp
            {
              intro a' b' eqa' neqa'
              rw [eqa'] at neqa'
              contradiction
            }
            {
              exact heq
            }
          }
          rw [hμeq] at hμneq
          trivial
        }
        {trivial}
      }
      {
        intro h
        unfold BEq.beq instBEqμ instBEq
        simp
        apply (NodeMap.fold_ind (P:=(fun b↦b=true)))
        {trivial}
        {
          intro a b bt
          rw [bt, h]
          trivial
        }
      }
    }

  instance {α β : Type} [NodeMap α] [ToString α] [ToString β] : ToString ⟦α, β⟧ where
    toString μ := μ fold⟪"", (fun nd repr => repr ++
      "\n{" ++ toString nd.data ++ ": " ++ toString (μ◃nd) ++ "}")⟫

  -- copied from Mathlib for utility
  class Preorder (α : Type) extends LE α where
    le_refl : ∀ a : α, a ≤ a
    le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c

  instance (α : Type) [Preorder α] : LE α where
    le := LE.le

  instance {α β : Type} [NodeMap α] [HasBot β] : HasBot ⟦α, β⟧ where
    bot :=  NodeMap.const (α:=α) ⊥

  instance {α β : Type} [NodeMap α] [Preorder β] : Preorder ⟦α , β⟧ := {
    le := LE.le
    le_refl := by {
      unfold LE.le instLEμ
      simp
      intros
      apply Preorder.le_refl
    }
    le_trans := by {
      unfold LE.le instLEμ
      simp
      intros
      rename_i a b c h₀ h₁ nd
      apply (Preorder.le_trans (a◃nd) (b◃nd) (c◃nd))
      apply h₀
      apply h₁
    }
  }

  /-
    A `DataflowProblem α β` extends an map constructor `NodeMap α` with choices of
    `τ : ⟦α, (β → β)⟧`, the node-indexed map of transition functions, and
    `σ : ⟦α, (List (Node α))⟧`, the node-indexed map of succesor lists fixing
    the graph topology. Two soundness theorems are requires relating the `≤`
    relation `τ`, and the `==` relation on `β` (as provided by their respective
    included typeclasses). The `⊔` and `≤` relations (on `⟦α, β⟧`), must also
    be proven.
  -/
  class DataflowProblem (α β : Type) extends NodeMap α, Max β, BEq β, Preorder β, HasBot β
  where
    τ : ⟦α, (β → β)⟧ -- transition functions
    σ : ⟦α, (List (Node α))⟧ -- successor relation

    τ_sound (α₀ : Node α) (β₀ β₁ : β) : (β₀ == β₁) → (τ◃α₀) β₀ == (τ◃α₀) β₁
    le_sound (β₀ β₁ β₂ : β) : (β₀ == β₁) → (β₀ ≤ β₂) → (β₁ ≤ β₂)

    map_le_supl (ν₀ ν₁ ν₂ : ⟦α, β⟧) (h : ν₀ ≤ ν₁) : (ν₀ ≤ (ν₁ ⊔ ν₂))
    map_le_supr (ν₀ ν₁ ν₂ : ⟦α, β⟧) (h : ν₀ ≤ ν₂) : (ν₀ ≤ (ν₁ ⊔ ν₂))

end Basics


/-
  The section `DataflowProblemSolver ` is paramterized on an instance of `DataflowProblem α β`.
  It builds on the definitions of maps `⟦α, β⟧` from `NodeMap α`, and on the transition functions
  `τ ◃ a` and succesor lists `σ ◃ a` for each node `a : Node α` (`◃` used as notation for map get)
  provided by the `DataflowProblem` to compute a series of utility values, functions, and soundness
  theorems ultimately definiting `DataflowProblem.solve`. This `solve` function performs a fixpoint
  search for a solution to this dataflow problem instance. Its return type :`Option ((ν : ⟦α, β⟧) ×' I' ν)`,
  captures that the search may fail, as it iterates only for a maximm of `(depth : ℕ) := 1000` rounds.
  The `some` case, on the other hand, provides `ν : ⟦α, β⟧` - the map from nodes to data `β` that solves
  the dataflow problem, and a `I' ν : Prop` - which captures that `ν` satisfies the dataflow problem.
-/
section DataflowProblemSolver
  variable {α β : Type} [BEq α] {DP: DataflowProblem α β}
  open DataflowProblem

  def ν₀ : ⟦α, (β × Bool)⟧ := ⟪↦(⊥, true)⟫

  def ε (a₀ a₁ : Node α) : Bool := List.elem a₁ (σ◃a₀)

  def strip_bools (ν : ⟦α, (β × Bool)⟧) := ν map⟪fun (β, _)=>β⟫

  def E (P : (Node α) → (Node α) → Prop) := ∀ (a₀ a₁) (_:ε a₀ a₁), P a₀ a₁
  def R (ν₀ : ⟦α, (β × Bool)⟧) (ν₁ : ⟦α, β⟧) [LE β]: Prop := E (fun a₀ a₁ => (ν₀◃a₀).2 ∨ (τ◃a₀) ((ν₀◃a₀).1) ≤ (ν₁◃a₁))
  def I (ν : ⟦α, (β × Bool)⟧) : Prop := R ν (strip_bools ν)

  def R' (ν₀ ν₁ : ⟦α, β⟧) : Prop := E (fun a₀ a₁ => (τ◃a₀) (ν₀◃a₀) ≤ ν₁◃a₁)
  def I' (ν : ⟦α, β⟧) : Prop := R' ν ν

  theorem base_case : @I α β _ DP ν₀ := by {
    unfold I R E
    intro α₀ α₁ edge
    left
    unfold ν₀
    rw [NodeMap.of_const_get]
  }

  def δ (ν : ⟦α, (β × Bool)⟧) (a : Node α) : ⟦α, β⟧ := -- step
    of_func⟪(fun a' => if ε a a' then ((τ◃a) (ν◃a).1) else ⊥)⟫

  def Δ₀ (ν : ⟦α, (β × Bool)⟧) : ⟦α, β⟧ :=
    ν fold⟪ν map⟪(·.1)⟫, (fun a ν₀ => if (ν◃a).2 then ν₀ ⊔ (δ ν a) else ν₀)⟫

  def Δ (ν : ⟦α, (β × Bool)⟧) : ⟦α, (β × Bool)⟧ :=
    let ν' := Δ₀ ν
    of_func⟪fun a => let (β, β') := ((ν◃a).1, (ν'◃a)); (β', β != β')⟫


  def is_fix (ν : ⟦α, (β × Bool)⟧) : Bool :=
    ν map⟪fun x↦x.2⟫ == ⟪↦false⟫

  omit [BEq α] in theorem is_fix_sound (ν : ⟦α, (β × Bool)⟧)
    : is_fix ν → ∀ a, !(ν ◃ a).2 := by {
      unfold is_fix
      intro h a
      have h' : (ν map⟪fun x => x.snd⟫)◃a == ⟪↦false⟫◃a := by {
        apply (NodeMap.beq_ext (ν map⟪fun x => x.snd⟫) ⟪↦false⟫).mp
        assumption
      }
      simp at h'
      rw [NodeMap.of_map_get, NodeMap.of_const_get] at h'
      rw [h']
      trivial
  }

  omit [BEq α] in theorem strip_bools_snd (ν : ⟦α, (β × Bool)⟧) (a : Node α)
    : ( (strip_bools ν)◃a = (ν◃a).1) := by {
      unfold strip_bools
      rw [NodeMap.of_map_get]
    }

  theorem δlessΔ (ν : ⟦α, (β × Bool)⟧) (a₀ : Node α) (h: (ν ◃ a₀).2): δ ν a₀ ≤ Δ₀ ν := by {
    let P a ν₀ := (ν◃a).2 = true → δ ν a ≤ ν₀
    apply (NodeMap.fold_strong_ind P)<;>try unfold P
    {
      intro a γ₀ ha
      rw [ha]
      simp
      apply map_le_supr
      apply Preorder.le_refl
    }
    {
      intro a γ₀ b ha ha'
      have h' := (ha ha')
      cases (ν◃b).2<;>simp
      assumption
      apply map_le_supl; assumption

    }
    assumption
  }

  theorem Δfpt (ν : ⟦α, (β × Bool)⟧) (a : Node α) (nb_eq:(Δ ν ◃ a).2 = false)
    : (ν ◃ a).1 == (Δ ν ◃ a).1 := by {
      unfold Δ
      simp
      rw [NodeMap.of_func_get]
      simp
      unfold Δ at nb_eq
      simp at nb_eq
      rw [NodeMap.of_func_get] at nb_eq
      simp at nb_eq
      unfold bne at nb_eq
      cases h : (ν◃a).1 == Δ₀ ν◃a
      {
        rw [h] at nb_eq
        contradiction
      }
      {
        rfl
      }
    }

  theorem Δmono (ν : ⟦α, (β × Bool)⟧) : (strip_bools ν) ≤ Δ₀ ν := by {
    let P ν' := (strip_bools ν) ≤ ν'
    apply NodeMap.fold_ind
    {
      unfold LE.le
      intro a
      rw [NodeMap.of_map_get]
      rw [strip_bools_snd]
      apply Preorder.le_refl
    }
    {
      intro a g h
      cases (ν◃a).2<;> simp
      assumption
      apply map_le_supl
      assumption
    }
  }

  theorem Δgrnd (ν : ⟦α, (β × Bool)⟧) : ∀ a, (Δ ν◃a).1 = (Δ₀ ν ◃ a) := by {
    intro a
    unfold Δ
    simp
    rw [NodeMap.of_func_get]
  }


  theorem Δlift (ν : ⟦α, (β × Bool)⟧) (a₀ a₁ : Node α) (edge : ε a₀ a₁) (h : I ν)
    : (τ◃a₀) (ν◃a₀).1 ≤ (Δ ν ◃ a₁).1 := by {
      cases b : (ν◃a₀).2
      {
        have le_fst : (τ◃a₀) (ν◃a₀).1 ≤ (ν◃a₁).1 := by {
          have h' := h a₀ a₁ edge
          simp at h'
          rw [b] at h'
          simp at h'
          rw [strip_bools_snd] at h'
          assumption
        }
        have le_snd : (ν◃a₁).1 ≤ (Δ₀ ν ◃ a₁) := by {
          have h':= Δmono ν a₁
          rw [strip_bools_snd] at h'
          assumption
        }
        rewrite [Δgrnd]
        exact (@Preorder.le_trans β _ _ _ _ le_fst le_snd)
      }
      {
      have le_fst : (τ◃a₀) (ν◃a₀).1 ≤ (δ ν a₀)◃a₁ := by {
        unfold δ
        rw [NodeMap.of_func_get, edge]
        apply Preorder.le_refl
      }
      have le_snd : (δ ν a₀)◃a₁ ≤ (Δ₀ ν ◃ a₁) := by {
        apply δlessΔ
        assumption
      }
      rewrite [Δgrnd]
      exact (@Preorder.le_trans β _ _ _ _ le_fst le_snd)
    }
  }

  theorem Δpres (ν : ⟦α, (β × Bool)⟧) (h : I ν) : I (Δ ν) := by {
    unfold I R E
    intro a₀ a₁ edge
    cases Δstat : (Δ ν◃a₀).2
    right; {
      {
        rw [strip_bools_snd]
        have Δrel := Δlift ν a₀ a₁ edge h

        have Δfpa : (ν ◃ a₀).1 == (Δ ν ◃ a₀).1 := by {
          have h' := Δfpt ν a₀
          rw [Δstat] at h'
          simp at h'
          assumption
        }
        have Δfpa_lift : (τ◃a₀) (ν ◃ a₀).1 == (τ◃a₀) (Δ ν ◃ a₀).1 := by {
          apply τ_sound
          exact Δfpa
        }
        apply le_sound (β₀:=(τ◃a₀) (ν◃a₀).1) <;> assumption
      }
    }
    left; rfl
  }

  theorem Δsol (ν : ⟦α, (β × Bool)⟧) (h₀ : I ν) (h₁ : is_fix ν = true)
    : I' (strip_bools ν) := by {
      unfold I' R' E
      unfold I R E at h₀

      intro a₀ a₁ edge
      have h₀' := h₀ a₀ a₁ edge
      have h₁' := (is_fix_sound ν h₁) a₀
      simp at h₀'

      cases h₂ : (ν◃a₀).2
      {
        cases h₀'
        {
          rename_i h₃
          rw [h₃] at h₂
          contradiction
        }
        {
          rw [strip_bools_snd]
          assumption
        }
      }
      {
        rw [h₂] at h₁'
        contradiction
      }
  }

  def DataflowProblem.solve_to_depth {α β : Type}
    (depth : ℕ)
    (DP : DataflowProblem α β)
    [BEq α]
    (ν : ⟦α, (β × Bool)⟧)
    (h : I ν)
    : Option ((ν : ⟦α, (β × Bool)⟧) ×' (I ν) ×' (is_fix ν) = true) :=
      match depth with
        | 0 => none
        | Nat.succ depth' =>
          let ν' := Δ ν
          let h' := Δpres ν h
          if fix : is_fix ν' then
            some ⟨ν', h', fix⟩
          else
            solve_to_depth depth' DP ν' h'

  def DataflowProblem.solve {α β : Type} [BEq α]
    (DP : DataflowProblem α β)
    : Option ((ν : ⟦α, β⟧) ×' I' ν)

    := (DP.solve_to_depth 1000 ν₀ base_case).map (fun ⟨ν, h, fix⟩ =>
      let ν' := strip_bools ν; ⟨ν', Δsol ν h fix⟩)

end DataflowProblemSolver

/-
  The section `FiniteDataflowProblemSolver` provides a structure type definition
  `FiniteSolverInput β`, that can be instantiated with any graph over
  `num_nodes : ℕ` nodes, with data of type `β`, as long as the edge relation and
  transition functions can be described by numbered node index. To fully instantiate
  a `FiniteSolverInput`, 4 simple soundness theorems relating largely the relations
  on `β` must be proved.
  `FiniteDataflowProblem ... FiniteSolverInput β → DataflowProblem ℕ β` is the
  key function, lifting a `FiniteSolverInput` to `DataflowProblem` admitting the
  solver function `DataflowProblem.solve`.
-/
section FiniteDataflowProblemSolver

  variable (n : Nat) -- number of nodes

  structure FiniteSolverInput (β : Type)
    [BEq β]
    [Preorder β]
    [Max β]
    [HasBot β]
  where
    num_nodes : ℕ
    edges : ℕ → ℕ → Bool
    transitions : ℕ → β → β

    transitions_sound n (β₀ β₁ : β) : (β₀ == β₁) → (transitions n) β₀ == (transitions n) β₁
    le_sound (β₀ β₁ β₂ : β) : (β₀ == β₁) → (β₀ ≤ β₂) → (β₁ ≤ β₂)
    le_supl (β₀ β₁ : β) : β₀ ≤ Max.max β₀ β₁
    le_supr (β₀ β₁ : β) : β₁ ≤ Max.max β₀ β₁

  def LtProp : NodeProp ℕ where
    node_prop n' := n' < n

  def NodeT := @Node ℕ (LtProp n)

  def node_to_fin (nd : NodeT n) : (Fin n)
    := {val := @nd.data, isLt := @nd.sound}

  def fin_to_node (fin : Fin n) : (NodeT n)
    := @Node.mk ℕ (LtProp n) fin.val fin.isLt

  def nodes : Vector (NodeT n) n
    := Vector.ofFn (fin_to_node n)

  def vector_fn {β : Type} (f : NodeT n → β) : Vector β n
    := Vector.ofFn (f ∘ (fin_to_node n))

  def FiniteNodeProp : NodeProp ℕ := {
      node_prop n' := n' < n
    }

  def FiniteNodeMap : NodeMap ℕ := {
    FiniteNodeProp n with
      μ β := Vector β n
      const β
        := vector_fn n (fun _ => β)
      of_func f
        := vector_fn n f
      get μ nd
        := μ.get (node_to_fin n nd)
      fold _ := (nodes n).toList.foldr
      app_unary μ f := Vector.map f μ
      app_binary μ₀ μ₁ f :=
        (nodes n).map (fun nd => f
          (μ₀.get (node_to_fin n nd))
          (μ₁.get (node_to_fin n nd)))

      of_const_get := by {
        intros
        unfold vector_fn Vector.get
        simp
      }
      of_func_get := by {
        intros
        unfold node_to_fin vector_fn Vector.get
        simp
        unfold fin_to_node
        rfl
      }
      of_map_get := by {
        intros
        unfold Vector.map Vector.get
        simp
      }
      of_app_binary_get := by {
        intros β₀ β₁ γ μ₀ μ₁ f a
        unfold Vector.map Vector.get node_to_fin nodes fin_to_node
        simp
      }

      fold_ind := by {
        intro β γ ν γ₀ acc P h₀ h₁
        induction ((nodes n).toList)
        {
          simp
          assumption
        }
        {
          rename_i hd tl Pfld
          simp
          apply h₁
          assumption
        }
      }

      fold_strong_ind := by {
        intro β γ ν γ₀ acc P h₀ h₁
        let Q l := ∀ nd ∈ l, P nd (List.foldr acc γ₀ l)
        have h : Q (nodes n).toList := by {
          induction (nodes n).toList<;>unfold Q; simp
          {
            rename_i hd tl Qtl
            intro nd ndin
            cases ndin
            {
              apply h₀
            }
            {
              simp
              apply h₁
              apply Qtl
              assumption
            }
          }
        }
        unfold Q at h
        intro a
        apply h
        simp
        unfold nodes Vector.ofFn
        simp
        cases a
        rename_i d snd
        exists Fin.mk d snd
      }
  }

  /-
    This takes a defined `FiniteSolverInpu β` and generates a `DataflowProblem ℕ β`.
    This is the end of the section because the returned instance provides the
    `DataflowProblem.solve` function.
  -/
  def FiniteDataflowProblem {β : Type}
    [BEq β]
    [P:Preorder β]
    [Max β]
    [HasBot β]
    (FSI : FiniteSolverInput β)
    : DataflowProblem ℕ β
    := let FNM := FiniteNodeMap n;
      {
      τ := vector_fn n (FSI.transitions ·.data)
      σ := vector_fn n (fun nd =>
            (nodes n).toList.filter (FSI.edges nd.data ·.data)
          )

      τ_sound := by {
        intro α₀ β₀ β₁ beq
        unfold vector_fn Vector.ofFn NodeMap.get
        unfold FNM FiniteNodeMap Vector.get fin_to_node node_to_fin
        simp
        apply FSI.transitions_sound
        assumption
      }

      le_sound := FSI.le_sound

      map_le_supl := by {
        unfold LE.le instLEμ Max.max instMaxμ
        simp
        intro ν₀ ν₁ ν₂ h a
        unfold NodeMap.app_binary NodeMap.get
        unfold FNM FiniteNodeMap node_to_fin Vector.map Vector.get nodes fin_to_node
        simp
        apply Preorder.le_trans
        {apply h}
        {apply FSI.le_supl}
      }
      map_le_supr := by {
        unfold LE.le instLEμ Max.max instMaxμ
        intro ν₀ ν₁ ν₂ h a
        unfold NodeMap.app_binary NodeMap.get FNM
        unfold FiniteNodeMap node_to_fin Vector.map Vector.get nodes fin_to_node
        simp
        apply Preorder.le_trans
        {apply h}
        {apply FSI.le_supr}
      }
    }
end FiniteDataflowProblemSolver

/-
  The section `InnerMapImpl` provides a further reification of the
  `DataflowProblem`-generating pipeline built above. In particular,
  It makes instantiating `FiniteSolverInput β` easy for datatypes `β`
  that represent maps themselves from a finite set of keys to values.

  Motivation:

  To instantiate the above `FiniteSolverInput β` for types `β`, that have
  boolean equality (`BEq β`), a compatible ordering relation
  (`Preorder β`), a supremum wrt ord `Max β`), a bottom element wrt ord
  (`HasBot β`), and appropriate congruences under equality, is easy.

  For example: `FiniteSolverInput ℕ` or even `List ℕ` or other structures
  with sufficiently many library typeclass instances.

  However, for many dataflow analysis cases, the right datatype `β` is
  itself a map type. for example `⟦ℕ, γ⟧` for an innter datatype `γ`.
  `ℕ` here is chosen to accomodate mappings over any finite, numbered
  set of keys. `γ` must provide all the structure requires of `β` itself,
  however, it will ideally be a simple enough type that this is immediate.
  Finite types will often suffice for `γ` (e.g. `Bool` for use/free), and
  in other cases shallow inductive types like the `ℂ` for constancy of a
  value (set to n:ℕ, set to some value, unknown).
  mappings `β := ⟦ℕ, γ⟧` represents assignments of each of the `num_keys`
  keys (e.g., variable names, mem locs, other identifiers) to data `γ`.

  To complete the `DataflowProblem` instance, the edge relation `edges`
  must be provided, and the transitions `τ := transitions n k`. Here
  `τ` is the transition function at node  `n < num_nodes`, as it acts
  on key `k < num_keys`. Notably, the "whole node" functions `⟦ℕ, γ⟧ → ⟦ℕ, γ⟧`
  that can be derived by thus specifying the transitions are only those
  that factor into components that each act on a single key. This is a
  restriction of `InnerMapImpl`.

  `InnerMapImpl.SolutionT` is a type that provides a final assignment
  of nodes to data `β`, and of indexed props establishing the
  satisfaction of the dataflow constraints by these data.

  `InnerMapImpl.Solution` returns a `Option (SolutionT ...)`. This
  represents the success vs timeout case.

  That's how this thing works! 💕
-/
section InnerMapImpl
  variable (ρ : Type) [DecidableEq ρ] [Preorder ρ] [DecidableLE ρ] [Max ρ] [HasBot ρ]
  variable (le_supl:∀ ρ₀ ρ₁ : ρ, ρ₀ ≤ ρ₀ ⊔ ρ₁)
  variable (le_supr:∀ ρ₀ ρ₁ : ρ, ρ₁ ≤ ρ₀ ⊔ ρ₁)
  variable (num_nodes num_keys : ℕ)
  variable (edges : ℕ → ℕ → Bool)
  variable (transitions : ℕ → ℕ → ρ → ρ)

  /-
    `SolutionT` captures the type of information returned by this section's
    computqtions to the caller. namely, it forgets internal data representation
    and offers all indexing by raw `(ℕ → ⬝).

    It is returned by `Solution` below
  -/
  section SolutionImpl
    structure SolutionT where
      vals (n k : ℕ) : (n < num_nodes) → (k < num_keys) → ρ
      props (n m k : ℕ) : (hn : n < num_nodes) → (hm : m < num_nodes) → (hk : k < num_keys) →
        (edges n m) → transitions n k (vals n k hn hk) ≤ (vals m k hm hk)

    def SolutionT.toString [ToString ρ]
    (𝕊 : SolutionT ρ num_nodes num_keys edges transitions)
    : String :=
      let 𝕍 := 𝕊.vals
      let nd_to_string n (hn :n < num_nodes) : String :=
        let entries := (List.range num_keys).filterMap
          (fun k => if hk: k < num_keys then some (ToString.toString (𝕍 n k hn hk)) else none)
        String.intercalate " " entries
      let lines := (List.range num_nodes).filterMap
        (fun n => if hn: n < num_nodes then (
          let s := nd_to_string n hn; some (s!"Node {n}: {s}")
        ) else none)
      String.intercalate "\n" ([""] ++ lines ++ [""])

      instance [ToString ρ] : ToString (SolutionT ρ num_nodes num_keys edges transitions) where
        toString := (SolutionT.toString ρ num_nodes num_keys edges transitions)

  end SolutionImpl

  /-
    This is the `NodeMap ℕ` instance for INNER maps over num_keys
    Outer maps over num_nodes have a separate `NodeMap ℕ` instance.
    This is because these provide different types `Node ℕ`; both
    are finite types, but of different size.

    confusion over this duality is resolved where necessary by
    providing identifiers to contextual instances, as opposed
    to relying on inference at the signature level.

    For example, FNM below captures the INNER map types, whereas
    the outer type is inferred without its invocation. Later,
    `Solution` binds identifiers (`NMN` and `NMK`) to each of the
    (`n`-indexed and `k`-indexed) `NodeMap ℕ` instances.

    Later in `Solution`, nodes `Node ℕ` corresponding to indices
    of each of the inner and outer maps are needed, and are obtained:
      `ndk : @Node ℕ NMK.toNodeProp := @Node.mk ℕ NMK.toNodeProp k`
      `ndn : @Node ℕ NMN.toNodeProp := @Node.mk ℕ NMN.toNodeProp n`

    Though dealing with dual instances of `NodeMap ℕ` is cumbersome,
    it allows significant code reuse and defines dataflowproblems
    with `β` equal to a map type minimally.
  -/
  def FNM : NodeMap ℕ := (FiniteNodeMap num_keys)

  /-
    Defining a `FiniteSolverInput ⟦ℕ, ρ⟧` requires
    tweaking the `transitions` function to index on
    `Node ℕ`s instead of `ℕ`s, and proving a small
    handful of compatibility lemmas. They ultimately
    rely on sufficient corresponding properties of
    `ρ` through unrollings also dependent on above-
    proven properties of `⟦⬝, ⬝⟧` types. None are
    very surprising.
  -/
  def FSI {_:NodeMap ℕ}: FiniteSolverInput (⟦ℕ, ρ⟧) := {
    num_nodes := num_nodes
    edges := edges
    transitions n β₀ := of_func⟪fun k ↦ transitions n k.data (β₀◃k)⟫

    transitions_sound := by {
      intro a β₀ β₁ βq
      apply (NodeMap.beq_ext _ _).mpr
      intro a
      rw [NodeMap.of_func_get]
      rw [NodeMap.of_func_get]
      have h : β₀◃a == β₁◃a := by {
        apply (NodeMap.beq_ext β₀ β₁).mp
        assumption
      }
      have h' : β₀◃a = β₁◃a := by {
        unfold BEq.beq instBEqOfDecidableEq at h
        simp at h
        assumption
      }
      rw [h']
      apply BEq.refl
    }

    le_sound := by {
      unfold LE.le instLEOfPreorder Preorder.toLE instPreorderμ instLEμ
      simp
      intro β₀ β₁ β₂ eq₀₁ le₀₂ α
      have h : β₀◃α == β₁◃α := by {
        apply (NodeMap.beq_ext _ _).mp
        assumption
      }
      unfold BEq.beq instBEqOfDecidableEq at h
      simp at h
      rw [←h]
      apply le₀₂
    }

    le_supl := by {
      unfold LE.le instLEOfPreorder Preorder.toLE instPreorderμ instLEμ
      simp
      intro β₀ β₁ a
      unfold Max.max instMaxμ
      simp
      rw [NodeMap.of_app_binary_get]
      apply le_supl
    }

    le_supr := by {
      unfold LE.le instLEOfPreorder Preorder.toLE instPreorderμ instLEμ
      simp
      intro β₀ β₁ a
      unfold Max.max instMaxμ
      simp
      rw [NodeMap.of_app_binary_get]
      apply le_supr
    }
  }

  /-
    `Solution` mainly functions to take the `FSI : FiniteSolverInput ⟦ℕ, ρ⟧`
    from above, use `FiniteDataflowProblem` from above to construct a
    `DataflowProblem ℕ ⟦ℕ, ρ⟧` (internally represented by a `⟦ℕ, ⟦ℕ, ρ⟧⟧` instance),
    and map under the resultant `Option ((ν : ⟦ℕ, ⟦ℕ, ρ⟧⟧) ×' I' ν)` a transformation
    to the `InnerMapImpl.SolutionT` type. This mapping requires folding
    and unfolding many conversions between raw `ℕ` indices, and proof-carrying
    `Node ℕ` instances (of each `NodeMap ℕ` class!). None of these proofs
    are surprising.
  -/
  def Solution : Option (SolutionT ρ num_nodes num_keys edges transitions) :=
    let NMK : NodeMap ℕ := FNM num_keys
    let DP : DataflowProblem ℕ ⟦ℕ, ρ⟧ := FiniteDataflowProblem num_nodes
      (FSI ρ le_supl le_supr num_nodes edges transitions)
    let NMN := DP.toNodeMap
    match DP.solve with
    | none => none
    | some ⟨ν, h⟩ =>
      let vals n k hn hk : ρ := (ν.get ⟨n, hn⟩).get ⟨k, hk⟩

      let props n m k hn hm hk : (edges n m) →
        transitions n k (vals n k hn hk) ≤ vals m k hm hk := by {
          unfold I' R' E at h
          intro e
          let ndn : @Node ℕ NMN.toNodeProp := ⟨n, by {
            unfold NodeProp.node_prop NodeMap.toNodeProp NMN DataflowProblem.toNodeMap DP FiniteDataflowProblem FiniteNodeMap FiniteNodeProp
            simp
            assumption
          }⟩
          let ndm : @Node ℕ NMN.toNodeProp := ⟨m, by {
            unfold NodeProp.node_prop NodeMap.toNodeProp NMN DataflowProblem.toNodeMap DP FiniteDataflowProblem FiniteNodeMap FiniteNodeProp
            simp
            assumption
          }⟩
          let ndk : @Node ℕ NMK.toNodeProp := @Node.mk ℕ NMK.toNodeProp k (by {
            unfold NodeProp.node_prop NodeMap.toNodeProp NMK FNM FiniteNodeMap FiniteNodeProp
            simp
            assumption
          })
          have hε : ε ndn ndm := by {
            unfold ε DataflowProblem.σ DP FiniteDataflowProblem FSI nodes vector_fn fin_to_node NodeMap.get FiniteNodeMap node_to_fin Vector.ofFn Vector.get
            simp
            exists ndm
            constructor
            exists ⟨m, hm⟩
            constructor
            unfold BEq.beq instBEqNode
            simp
            unfold ndn ndm
            simp
            assumption
          }
          have h' := h ndn ndm hε ndk
          simp at h'
          unfold DataflowProblem.τ DP FiniteDataflowProblem FSI NodeMap.get NodeMap.of_func FiniteNodeMap vector_fn fin_to_node node_to_fin NMK Vector.ofFn Vector.get FNM FiniteNodeMap vector_fn Vector.ofFn node_to_fin fin_to_node Vector.get at h'
          simp at h'
          apply h'
      }
      some {
        vals := vals
        props := props
      }
end InnerMapImpl

section ConcreteMapImpl
  section IsConstImpl
    inductive ℂ : Type where
      | maybe : ℂ -- key at pos may or may not be set (top val)
      | any : ℂ -- key at pos is set
      | some : ℕ → ℂ -- key at pos is set to (ℕ)
      | unreachable : ℂ -- false - key as pos is unreachable
      deriving DecidableEq

    notation "𝕄" => ℂ.maybe
    notation "𝔸" => ℂ.any
    notation "𝕊" => ℂ.some
    notation "𝕌" => ℂ.unreachable

    instance : ToString ℂ where
      toString := fun
      | 𝕄 => "𝕄"
      | 𝔸 => "𝔸"
      | 𝕊 n => s!"𝕊 {n}"
      | 𝕌 => "𝕌"

    instance : DecidableEq ℂ := by {
      unfold DecidableEq
      intro a b
      by_cases h: (a=b)
      apply isTrue; assumption
      apply isFalse; assumption
      }

    instance : Max ℂ where
      max := fun
      | 𝕄, _
      | _, 𝕄 => 𝕄 -- properties of merging w top (maybe - 𝕄) (if either branch is 𝕄, merge in 𝕄)
      | 𝕌, ℂ₀
      | ℂ₀, 𝕌 => ℂ₀ -- properties of merging w bot (unreachable - 𝕌) (if either branch is 𝕌, other is unaffected)
      | 𝕊 a, 𝕊 b => if a = b then 𝕊 a else 𝔸 --two 𝕊 (some) branches either agree, or must be generalized to 𝔸
      |_, _ => 𝔸 -- case where one branch is 𝔸 (any) and the other is 𝕊 (some), merge is 𝔸

    instance : HasBot ℂ where
      bot := 𝕌

    instance : Preorder ℂ where
      le ℂ₀ ℂ₁ := ℂ₁ = ℂ₀ ⊔ ℂ₁
      le_refl := by {
        intro ℂ₀
        cases ℂ₀<;>
        unfold Max.max instMaxℂ<;>
        simp
      }
      le_trans := by {
        unfold Max.max instMaxℂ<;>
        intro ℂ₀ ℂ₁ ℂ₂ r₀ r₁<;>
        cases ℂ₀<;>cases ℂ₁<;>cases ℂ₂<;>
        simp<;>simp at r₀<;>simp at r₁
        {
          rename_i n₀ n₁ n₂
          by_cases h₀₁: (n₀ = n₁) = true <;>
          simp at h₀₁ <;>
          by_cases h₁₂: (n₁ = n₂) = true <;>
          simp at h₁₂ <;>
          by_cases h₀₂: (n₀ = n₂) = true <;>
          simp at h₀₂ <;>
          try {split at r₀<;> contradiction} <;>
          try {split at r₁<;> contradiction}
          {rw [h₀₂]; simp}
          {rw [←h₀₁] at h₁₂; contradiction}
        }
    }

    instance : DecidableLE ℂ := by {
      intro ℂ₀ ℂ₁
      unfold LE.le instLEOfPreorder Preorder.toLE instPreorderℂ
      simp
      by_cases h : (ℂ₁ = ℂ₀⊔ℂ₁)
      apply isTrue; assumption
      apply isFalse; assumption
    }

    #synth DecidableEq ℂ
    #synth Preorder ℂ
    #synth DecidableLE ℂ
    #synth Max ℂ
    #synth HasBot ℂ

    theorem le_supl: ∀ ℂ₀ ℂ₁ : ℂ, ℂ₀ ≤ ℂ₀ ⊔ ℂ₁ := by {
      intro ℂ₀ ℂ₁
      unfold LE.le instLEOfPreorder Preorder.toLE instPreorderℂ Max.max instMaxℂ
      simp
      cases ℂ₀ <;> cases ℂ₁ <;> simp
      split <;> simp
    }
    theorem le_supr : ∀ ℂ₀ ℂ₁ : ℂ, ℂ₁ ≤ ℂ₀ ⊔ ℂ₁ := by {
      intro ℂ₀ ℂ₁
      unfold LE.le instLEOfPreorder Preorder.toLE instPreorderℂ Max.max instMaxℂ
      simp
      cases h₀ : ℂ₀ <;> cases h₁ : ℂ₁ <;> simp
      split <;> simp
      {
        rename_i n₀ n₁ eq
        rw [eq]
        simp
      }
    }
  end IsConstImpl

  def num_nodes : ℕ := 20
  def num_keys : ℕ := 2

  def edges : ℕ → ℕ → Bool := fun
  | 0, 1
  | 0, 2
  | 1, 3
  | 2, 4
  | 2, 5
  | 2, 6
  | 3, 7
  | 4, 3
  | 4, 8
  | 5, 9
  | 6, 10
  | 7, 1
  | 7, 11
  | 8, 12
  | 9, 13
  | 10, 13
  | 11, 15
  | 12, 14
  | 13, 14
  | 14, 16
  | 15, 16
  | 17, 18
  | 18, 19 => true
  | _, _ => false

  def transitions : ℕ → ℕ → ℂ → ℂ := fun
  | 0, _, _ => 𝕄
  | 2, 0, _ => ℂ.some 5
  | 2, 1, _ => ℂ.some 2
  | 5, 0, _ => ℂ.some 1
  | 6, 0, _ => ℂ.some 1
  | 7, 1, _ => ℂ.some 4
  | 8, 0, _ => ℂ.some 3
  | 11, 0, _ => ℂ.some 9
  | 14, 0, _ => ℂ.some 7
  | _, _, ℂ₀ => ℂ₀

  def 𝕏 := Solution
    (ρ:=ℂ)
    (le_supl:=le_supl)
    (le_supr:=le_supr)
    (num_nodes:=num_nodes)
    (num_keys:=num_keys)
    (edges:=edges)
    (transitions:=transitions)

  #eval 𝕏
  /- Output: (i looked at it by hand and it looks right 😊)

  some (
  Node 0: 𝕌 𝕌
  Node 1: 𝕄 𝕄
  Node 2: 𝕄 𝕄
  Node 3: 𝕄 𝕄
  Node 4: 𝕊 5 𝕊 2
  Node 5: 𝕊 5 𝕊 2
  Node 6: 𝕊 5 𝕊 2
  Node 7: 𝕄 𝕄
  Node 8: 𝕊 5 𝕊 2
  Node 9: 𝕊 1 𝕊 2
  Node 10: 𝕊 1 𝕊 2
  Node 11: 𝕄 𝕊 4
  Node 12: 𝕊 3 𝕊 2
  Node 13: 𝕊 1 𝕊 2
  Node 14: 𝔸 𝕊 2
  Node 15: 𝕊 9 𝕊 4
  Node 16: 𝔸 𝔸
  Node 17: 𝕌 𝕌
  Node 18: 𝕌 𝕌
  Node 19: 𝕌 𝕌
  ))

  -/
end ConcreteMapImpl
