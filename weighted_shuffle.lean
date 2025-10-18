import Std

/--
Radix of the tree.
-/
def ℝ : Nat := 9

abbrev Element : Type := Vector Nat (ℝ - 1)
def empty_element : Element := .replicate (ℝ - 1) 0

structure WeightedTree where
  internal_node_count : Nat
  tree : Vector Element internal_node_count
  total_count : Nat
  total_weight : Nat
  unremoved_count : Nat
  unremoved_weight : Nat
  height : Nat

  /--
    If `height` is not zero, then neither is `internal_node_count`.
  -/
  height_implies_node_count : height ≠ 0 → internal_node_count ≠ 0

theorem computeHeight_termination {num_elements powRh : Nat} (h : ¬num_elements ≤ powRh) (d : powRh ≠ 0) :
    num_elements - (powRh * ℝ) < num_elements - powRh := by
  simp_wf
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_not_le
    exact h
  · rewrite (occs := .pos [1]) [← Nat.mul_one powRh]
    apply Nat.mul_lt_mul_of_pos_left
    · decide -- ℝ > 1
    · exact Nat.pos_of_ne_zero d

def computeHeight (num_elements : Nat) : Nat × Nat :=
  let rec go (height internal powRh : Nat) (d : powRh ≠ 0) : Nat × Nat :=
    if num_elements ≤ powRh then
      (height, internal)
    else
      have powRh_pos := Nat.pos_of_ne_zero d
      go (height + 1) (internal + powRh) (powRh * ℝ)
        (Nat.ne_of_gt (Nat.mul_pos powRh_pos (by decide)))
  termination_by num_elements - powRh
  decreasing_by apply computeHeight_termination <;> assumption
  go 0 0 1 (by decide)

#guard computeHeight 0 = (0, 0)
#guard computeHeight 1 = (0, 0) -- Only the root node, which is implied in the total sum.
#guard computeHeight 384 = (3, 91)
#guard computeHeight 1024 = (4, 820)

def mkWeightedTree (num_elements : Nat) : WeightedTree :=
  let heights := computeHeight num_elements
  let tree := Vector.replicate heights.2 empty_element
  { tree := tree
    height := heights.1
    internal_node_count := heights.2

    total_count := 0
    total_weight := 0
    unremoved_count := 0
    unremoved_weight := 0

    height_implies_node_count := sorry -- TODO
  }

instance : Inhabited WeightedTree where
  default := mkWeightedTree 0

/--
  Updates the left sums in an element. Broadcasts `weight` to  [child_index, ℝ - 1) elements.
-/
def addWeight_updateSums (parent : Element) (child_index : Fin (ℝ - 1)) (weight : Nat) : Element :=
  let rec go (k : Nat) (hk : k < ℝ - 1) (acc : Element) : Element :=
    let acc := acc.set k (acc.get ⟨k, hk⟩ + weight) hk
    if hn : k + 1 < ℝ - 1 then
      go (k + 1) (hn) acc
    else
      acc
  go child_index.val child_index.isLt parent

/--
 Adds weight to the tree. Requires a prop `h` that the weight is not zero, as this
 tree implementation does not support having zero weight nodes.

 Returns `None` if there are more active nodes than `num_elements`.
-/
def addWeight? (t : WeightedTree) (weight : Nat) (_ : weight ≠ 0) : Option WeightedTree :=
  if count_in_bounds : t.unremoved_count ≤ t.internal_node_count then
    let V : Type := Vector Element t.internal_node_count
    let F : Type := Fin (ℝ * t.internal_node_count)
    let rec loop (i : F) (height_remaining : Nat) (tree : V) : V :=
      match height_remaining with
      | 0 => tree
      | Nat.succ height' =>
          let parent : Fin t.internal_node_count := ⟨(i - 1) / ℝ, by
            apply Nat.div_lt_of_lt_mul
            apply Nat.sub_lt_of_lt
            exact i.isLt
          ⟩
          let child : Fin ℝ := ⟨(i - 1) - (ℝ * parent), by
            rw [← Nat.mod_eq_sub_mul_div]
            exact Nat.mod_lt _ (by decide)
          ⟩
          let updated := Id.run do
              if chk : child < (ℝ - 1) then
                tree.set parent (addWeight_updateSums tree[parent] (child.castLT chk) weight)
              else
                tree -- Nothing to update
          let parent' : F := parent.castLE (Nat.le_mul_of_pos_left _ (by decide))
          loop parent' height' updated

    if h_ne_zero : t.height ≠ 0 then
      let i : F := ⟨t.internal_node_count + t.unremoved_count, by
        calc
          t.internal_node_count + t.unremoved_count
            ≤ 2 * t.internal_node_count := by
              rewrite [Nat.mul_comm, Nat.mul_two]
              apply Nat.add_le_add_left count_in_bounds
          _ < ℝ * t.internal_node_count := by
            rewrite [Nat.mul_lt_mul_right]
            . decide
            . exact Nat.zero_lt_of_ne_zero (t.height_implies_node_count h_ne_zero)
      ⟩
      have i_ne_zero : t.internal_node_count + t.unremoved_count ≠ 0 := by
        intro contra
        have := Nat.eq_zero_of_add_eq_zero_right contra
        exact (t.height_implies_node_count h_ne_zero) this
      let updated_elements := loop i t.height t.tree

      some { t with
        tree := updated_elements
        unremoved_count := t.unremoved_count + 1
        total_count := t.total_count + 1
        unremoved_weight := t.unremoved_weight + weight
        total_weight := t.total_weight + weight }
    else
      some { t with
        unremoved_count := t.unremoved_count + 1
        total_count := t.total_count + 1
        unremoved_weight := t.unremoved_weight + weight
        total_weight := t.total_weight + weight }
  else none


def example_tree : WeightedTree := mkWeightedTree 7
#eval! (((((((example_tree
  |> fun t => addWeight? t 100 (by decide)).get!
  |> fun t => addWeight? t 80  (by decide)).get!
  |> fun t => addWeight? t 50  (by decide)).get!
  |> fun t => addWeight? t 31  (by decide)).get!
  |> fun t => addWeight? t 27  (by decide)).get!
  |> fun t => addWeight? t 14  (by decide)).get!
  |> fun t => addWeight? t 6  (by decide)).get!
