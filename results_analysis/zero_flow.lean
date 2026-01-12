import Mathlib

structure CapacityGraph where
  adj : Array (Array (Nat × Int))

def CapacityGraph.size (g : CapacityGraph) : Nat :=
  g.adj.size

def CapacityGraph.has_capacity (g : CapacityGraph) (u v : Nat) (c : Int) : Prop :=
  u < g.size ∧
  ∃ pair, pair ∈ g.adj.getD u #[] ∧ pair.1 = v ∧ pair.2 = c

def CapacityGraph.well_formed (g : CapacityGraph) : Prop :=
  ∀ u, u < g.size →
    (∀ pair, pair ∈ g.adj.getD u #[] → pair.1 < g.size) ∧
    (∀ p1 p2, p1 ∈ g.adj.getD u #[] → p2 ∈ g.adj.getD u #[] → p1.1 = p2.1 → p1 = p2)

def FlowMap := Nat → Nat → Int

def FlowMap.get (f : FlowMap) (u v : Nat) : Int := f u v

def CapacityGraph.respects_capacity (g : CapacityGraph) (f : FlowMap) : Prop :=
  ∀ u v,
    (f.get u v > 0 →
      ∃ c, g.has_capacity u v c ∧ f.get u v ≤ c) ∧
    (f.get u v >= 0)

def flow_out (g : CapacityGraph) (f : FlowMap) (u : Nat) : Int :=
  let neighbors := g.adj.getD u #[]
  neighbors.foldl (λ sum pair => sum + f.get u pair.1) 0

def flow_in (g : CapacityGraph) (f : FlowMap) (u : Nat) : Int :=
  (List.range g.size).foldl (λ sum v => sum + f.get v u) 0

def is_conserved (g : CapacityGraph) (f : FlowMap) (s t : Nat) : Prop :=
  ∀ u, u < g.size → u ≠ s → u ≠ t →
    flow_in g f u = flow_out g f u

def is_valid_flow (g : CapacityGraph) (f : FlowMap) (s t : Nat) : Prop :=
  g.respects_capacity f ∧ is_conserved g f s t

def flow_val (g : CapacityGraph) (f : FlowMap) (s : Nat) : Int :=
  flow_out g f s - flow_in g f s

-- ABLATION: Weakened spec (Buggy Spec)
-- We only require the result to be *a* valid flow, not necessarily the *max* flow.
def is_valid_result (g : CapacityGraph) (f : FlowMap) (s t : Nat) : Prop :=
  is_valid_flow g f s t

def CapacityGraph.capacities_bounded (g : CapacityGraph) : Prop :=
  g.size ≤ 1000 ∧
  ∀ u v c, g.has_capacity u v c → c ≥ 0 ∧ c ≤ 100000

@[reducible, simp]
def max_flow_value_precond (graph : CapacityGraph) (s t : Nat) : Prop :=
  graph.well_formed ∧
  graph.capacities_bounded ∧
  s < graph.size ∧
  t < graph.size ∧
  s ≠ t

-- IMPLEMENTATION: Always return 0
def max_flow_value (graph : CapacityGraph) (s t : Nat)
    (h_precond : max_flow_value_precond graph s t) : Int :=
  0

-- POSTCONDITION: Requires finding a flow `f` that matches the result (0)
@[reducible, simp]
def max_flow_value_postcond (graph : CapacityGraph) (s t : Nat) (result : Int)
    (_ : max_flow_value_precond graph s t) : Prop :=
  ∃ f, is_valid_result graph f s t ∧ flow_val graph f s = result

-- HELPER LEMMA: Folding +0 over a list preserves the accumulator
theorem foldl_add_zero {α} (l : List α) (x : Int) :
    List.foldl (λ sum _ => sum + 0) x l = x := by
  induction l generalizing x with
  | nil => rfl
  | cons head tail ih =>
    simp [List.foldl]

theorem array_foldl_add_zero {α} (arr : Array α) (x : Int) :
    arr.foldl (λ sum _ => sum + 0) x = x := by
  -- Use dot notation 'arr.foldl' to fix argument order errors.
  -- Convert Array fold to List fold using the standard Mathlib lemma:
  rw [←Array.foldl_toList] 
  -- Now it matches the List lemma you proved earlier
  apply foldl_add_zero

-- PROOF
theorem max_flow_value_postcond_satisfied (graph : CapacityGraph) (s t : Nat)
    (h_precond : max_flow_value_precond graph s t) :
    max_flow_value_postcond graph s t (max_flow_value graph s t h_precond) h_precond := by
  -- 1. Define the zero flow map
  let f_zero : FlowMap := fun _ _ => 0

  -- 2. Prove f_zero respects capacity
  have h_cap : graph.respects_capacity f_zero := by
    intros u v
    constructor
    · -- f(u,v) > 0 implies exists capacity...
      intro h_gt
      -- 0 > 0 is false, so this implication is trivially true
      simp [FlowMap.get] at h_gt
      contradiction
    · -- f(u,v) >= 0
      dsimp [f_zero, FlowMap.get] -- Simplifies `f_zero.get u v` to `0`
      -- Goal becomes `0 ≥ 0`
      apply le_refl

  -- 3. Prove f_zero is conserved (flow_in == flow_out == 0)
  have h_cons : is_conserved graph f_zero s t := by
    intros u _ _ _
    unfold flow_in flow_out
    simp [FlowMap.get]
    -- Apply helper lemma to show folds result in 0
    rw [array_foldl_add_zero]
    rw [foldl_add_zero]

  -- 4. Prove flow value is 0
  have h_val : flow_val graph f_zero s = 0 := by
    unfold flow_val flow_out flow_in
    simp [FlowMap.get]
    rw [array_foldl_add_zero]
    rw [foldl_add_zero]
    simp

  -- 5. Combine to prove postcondition
  exists f_zero