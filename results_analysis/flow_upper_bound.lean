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
    -- Unique targets (Simple Graph Property)
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

-- IMPLEMENTATION: Sum of outgoing capacities from s
def max_flow_value (graph : CapacityGraph) (s t : Nat)
    (h_precond : max_flow_value_precond graph s t) : Int :=
  let neighbors := graph.adj.getD s #[]
  neighbors.foldl (λ sum pair => sum + pair.2) 0

-- POSTCONDITION: The result is an Upper Bound on any valid flow
@[reducible, simp]
def max_flow_value_postcond (graph : CapacityGraph) (s t : Nat) (result : Int)
    (_ : max_flow_value_precond graph s t) : Prop :=
  ∀ f, is_valid_flow graph f s t → flow_val graph f s ≤ result

-- --- LEMMAS ---

-- 1. Monotonicity of foldl (Proof Replacement for first sorry)
theorem list_foldl_mono {α} (l : List α) (f g : α → Int) (acc1 acc2 : Int) :
    (∀ x, x ∈ l → f x ≤ g x) →
    acc1 ≤ acc2 →
    List.foldl (λ sum x => sum + f x) acc1 l ≤ List.foldl (λ sum x => sum + g x) acc2 l := by
  induction l generalizing acc1 acc2 with
  | nil =>
    intro _ h_acc
    simp [List.foldl]
    exact h_acc
  | cons head tail ih =>
    intro h_le h_acc
    simp [List.foldl]
    apply ih
    · intros x hx
      apply h_le
      exact List.mem_cons_of_mem head hx
    · apply add_le_add h_acc
      apply h_le
      exact List.mem_cons_self

-- 2. Non-negative Sum (Proof Replacement for second sorry)
theorem foldl_sum_nonneg {α} (l : List α) (f : α → Int) (acc : Int) :
    acc >= 0 →
    (∀ x, x ∈ l → f x >= 0) →
    List.foldl (λ sum x => sum + f x) acc l >= 0 := by
  induction l generalizing acc with
  | nil =>
    intro h_acc _
    simp [List.foldl]
    exact h_acc
  | cons head tail ih =>
    intro h_acc h_f_nonneg
    simp [List.foldl]
    apply ih
    · apply add_nonneg h_acc
      apply h_f_nonneg
      exact List.mem_cons_self
    · intros x hx
      apply h_f_nonneg
      exact List.mem_cons_of_mem head hx

-- --- MAIN PROOF ---

theorem max_flow_value_postcond_satisfied (graph : CapacityGraph) (s t : Nat)
    (h_precond : max_flow_value_precond graph s t) :
    max_flow_value_postcond graph s t (max_flow_value graph s t h_precond) h_precond := by
  intro f h_valid
  unfold flow_val max_flow_value flow_out

  -- Step 1: Prove flow_in >= 0 so we can drop it
  --have h_flow_in_nonneg : flow_in graph f s >= 0 := by
  have h_flow_in_nonneg : flow_in graph f s >= 0 := by
    unfold flow_in
    rw [← List.foldl_map] 
    apply foldl_sum_nonneg
    · apply le_refl
    · intros val h_mem -- Rename 'v' to 'val' to clarify it's an Int value, not a node
      -- 1. Unwrap the map to find the original node index
      rw [List.mem_map] at h_mem
      rcases h_mem with ⟨u, _, h_eq⟩ 
      -- 2. Substitute the value back to f.get u s
      rw [← h_eq]
      -- 3. Apply the validity property using the node index 'u'
      exact (h_valid.left u s).2

  -- Step 2: Reduce inequality (flow_out - flow_in <= result) -> (flow_out <= result)
  apply le_trans (Int.sub_le_self _ h_flow_in_nonneg)

  -- Step 3: Switch to List view to use induction
  -- Using Array.foldl_toList as requested
  rw [← Array.foldl_toList]
  rw [← Array.foldl_toList]

  -- Step 4: Apply Monotonicity Lemma
  -- We prove that for every edge, flow(s, v) <= capacity(s, v)
  apply list_foldl_mono
  · intros pair h_mem_list
    -- Convert List membership to Array membership for lemmas
    have h_mem_arr : pair ∈ graph.adj.getD s #[] := by
      -- 1. Rewrite the goal (pair ∈ arr) to (pair ∈ arr.data)
      rw [Array.mem_def]
      -- 2. Since arr.toList is definitionally equal to arr.data, 
      --    h_mem_list (pair ∈ arr.toList) matches the goal exactly.
      exact h_mem_list

    let v := pair.1
    let cap := pair.2

    -- Case analysis on flow positivity
    by_cases h_pos : f.get s v > 0
    · -- Flow > 0: Must respect capacity
      have h_respects := (h_valid.left s v).1 h_pos
      rcases h_respects with ⟨c_real, h_has_cap, h_le_real⟩

      -- Use Uniqueness Property from well_formed
      -- h_has_cap guarantees an edge exists in the list with capacity c_real
      rcases h_has_cap with ⟨_, ⟨p_real, h_mem_real, h_eq_v, h_eq_c⟩⟩

      -- Retrieve uniqueness proof from precondition
      have h_unique := h_precond.1 s (by exact h_precond.2.2.1)
      rcases h_unique with ⟨_, h_distinct⟩

      -- Prove p_real must be exactly `pair` because they share target `v`
      have h_same_pair : p_real = pair := by
        apply h_distinct p_real pair h_mem_real h_mem_arr
        rw [h_eq_v]

      -- Substitute back
      rw [h_same_pair] at h_eq_c
      rw [← h_eq_c] at h_le_real
      exact h_le_real

    · -- Flow <= 0
      simp at h_pos
      -- Prove capacity >= 0 from global bounds
      have h_cap_nonneg : cap >= 0 := by
        -- 1. First, prove the edge exists (satisfies has_capacity)
        have h_has_edge : graph.has_capacity s v cap := by
          unfold CapacityGraph.has_capacity
          constructor
          · exact h_precond.2.2.1 -- s < size
          · exists pair

        -- 2. Now feed this proof into the global bounds property
        -- h_precond.2.1.2 is the forall statement. 
        -- Applying s, v, cap, and h_has_edge gives us (cap >= 0 ∧ cap <= 100000)
        have h_bounds := h_precond.2.1.2 s v cap h_has_edge
        
        -- 3. Extract the left side (cap >= 0)
        exact h_bounds.1

      apply le_trans h_pos h_cap_nonneg

  · -- Initial accumulators are equal (0 <= 0)
    apply le_refl