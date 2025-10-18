import Std

/--
Radix of the tree.
-/
def R : Nat := 5

abbrev Element : Type := Vector Nat (R - 1)
def empty_element : Element := .replicate (R - 1) 0

structure WeightedTree where
  internal_node_count : Nat
  tree : Vector Element internal_node_count
  total_count : Nat
  total_weight : Nat
  unremoved_count : Nat
  unremoved_weight : Nat
  height : Nat

theorem computeHeight_lemma {numElements powRh : Nat} (h : ¬ numElements ≤ powRh) (d : powRh ≠ 0) :
    numElements - (powRh * R) < numElements - powRh := by
  simp_wf
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_of_not_le
    exact h
  · rewrite (occs := .pos [1]) [← Nat.mul_one powRh]
    apply Nat.mul_lt_mul_of_pos_left
    · decide -- R > 1
    · exact Nat.pos_of_ne_zero d

def computeHeight (numElements : Nat) : Nat × Nat :=
  let rec go (height internal powRh : Nat) (d : powRh ≠ 0) : Nat × Nat :=
    if numElements ≤ powRh then
      (height, internal)
    else
      have powRh_pos := Nat.pos_of_ne_zero d
      go (height + 1) (internal + powRh) (powRh * R)
        (Nat.ne_of_gt (Nat.mul_pos powRh_pos (by decide)))
  termination_by numElements - powRh
  decreasing_by apply computeHeight_lemma <;> assumption
  go 0 0 1 (by decide)

-- TODO: these assume R = 9
-- #guard computeHeight 0 = (0, 0)
-- #guard computeHeight 1 = (0, 0)
-- #guard computeHeight 384 = (3, 91)
-- #guard computeHeight 1024 = (4, 820)

def mkWeightedTree (numElements : Nat) : WeightedTree :=
  let heights := computeHeight numElements
  let tree := Vector.replicate heights.2 empty_element
  { tree := tree
    height := heights.1
    internal_node_count := heights.2

    total_count := 0
    total_weight := 0
    unremoved_count := 0
    unremoved_weight := 0 }

/--
  Updates the left sums in an element. Broadcasts `weight` to  [child_index, R - 1) elements.
-/
def addWeight_updateSums (parent_element : Element) (child_index : Fin (R - 1)) (weight : Nat) : Element :=
  let rec go (k : Nat) (hk : k < R - 1) (acc : Element) : Element :=
    let acc := acc.set k (acc.get ⟨k, hk⟩ + weight) hk
    if hn : k + 1 < R - 1 then
      go (k + 1) (hn) acc
    else
      acc
  go child_index.val child_index.isLt parent_element

/--
 Adds weight to the tree. Requires a prop `h` that the weight is not zero, as this
 tree implementation does not support having zero weight nodes.
-/
def addWeight (t : WeightedTree) (weight : Nat) (_ : weight ≠ 0) : WeightedTree :=
  let rec loop (i : Nat) (height_remaining : Nat) (tree : Vector Element t.internal_node_count) : Vector Element t.internal_node_count :=
    match height_remaining with
    | 0 => tree
    | Nat.succ height' =>
        let parent : Fin t.internal_node_count  :=
          ⟨(i - 1) / R, by
            sorry -- TODO
          ⟩
        let child_index : Fin R :=
          ⟨(i - 1) - (R * parent), by
            rw [← Nat.mod_eq_sub_mul_div]
            exact Nat.mod_lt _ (by decide)
          ⟩
        let updated := Id.run do
            if chk : child_index < (R - 1) then
              tree.set parent (addWeight_updateSums tree[parent] (child_index.castLT chk) weight)
            else
              tree -- Nothing to update
        loop parent height' updated
  let i := t.internal_node_count + t.unremoved_count
  let updatedElements := loop i t.height t.tree
  { t with
    tree := updatedElements
    unremoved_count := t.unremoved_count + 1
    total_count := t.total_count + 1
    unremoved_weight := t.unremoved_weight + weight
    total_weight := t.total_weight + weight }

def exampleTree : WeightedTree := mkWeightedTree 7
#eval! addWeight exampleTree 100  (by decide)
