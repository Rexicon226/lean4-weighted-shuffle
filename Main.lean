import Std
import Mathlib

/--
Radix of the tree.
-/
def R : Nat := 9

structure Element where
  left_sum : Vector Nat (R - 1)
  deriving Repr

structure WeightedTree where
  tree : Array Element

  total_count : Nat
  total_weight : Nat
  unremoved_count : Nat
  unremoved_weight : Nat
  internal_node_count : Nat
  height : Nat
  deriving Repr

def computeHeight (numElements : Nat) : Nat × Nat :=
  let rec go (height internal powRh : Nat) (d : powRh ≠ 0) : Nat × Nat :=
    if numElements ≤ powRh then
      (height, internal)
    else
      have powRh_pos := Nat.pos_of_ne_zero d
      go (height + 1) (internal + powRh) (powRh * R) (Nat.ne_of_gt (Nat.mul_pos powRh_pos (by decide)))
  termination_by numElements - powRh
  decreasing_by
    simp_wf
    apply Nat.sub_lt_sub_left
    . apply Nat.lt_of_not_le
      assumption
    .
      nth_rewrite 1 [← Nat.mul_one powRh]
      apply Nat.mul_lt_mul_of_pos_left
      . decide -- R is a constant, it's always > 1
      . exact Nat.pos_of_ne_zero d
  go 0 0 1 (by decide)

#guard computeHeight 0 = (0, 0)
#guard computeHeight 1 = (0, 0)
#guard computeHeight 384 = (3, 91)
#guard computeHeight 1024 = (4, 820)

def mkWeightedTree (numElements : Nat) : WeightedTree :=
  let heights := computeHeight numElements
  { tree := #[]
    total_count := numElements
    total_weight := 0
    unremoved_count := 0
    unremoved_weight := 0

    height := heights.1
    internal_node_count := heights.2 }

/--
 Adds weight to the tree. Requires a prop `h` that the weight is no zero, as this
 tree implementation does no support having zero weight nodes.
-/
def addWeight (t : WeightedTree) (weight : Nat) (_ : weight ≠ 0) : WeightedTree :=
  let rec loop (i : Nat) (h_rem : Nat) (tree : Array Element) : Array Element :=
    match h_rem with
    | 0 => tree
    | Nat.succ h' =>
        let parent := (i - 1) / R
        let child_index := (i - 1) / (R * parent) -- in [0, R) TODO: Fin proof
        let updated :=
          Id.run do
            let mut arr := tree
            let mut parentElement := arr[parent]'sorry -- TODO
            for k in [child_index : R] do
              parentElement := { parentElement with
                left_sum := parentElement.left_sum.set k (parentElement.left_sum[k]! + weight) sorry -- TODO
              }
            arr := arr.set parent parentElement sorry -- TODO
            arr
        loop parent h' updated
  let i := t.internal_node_count + t.unremoved_count
  let updatedElements := loop i t.height t.tree
  { t with
    tree := updatedElements
    unremoved_count := t.unremoved_count + 1
    total_count := t.total_count + 1
    unremoved_weight := t.unremoved_weight + weight
    total_weight := t.total_weight + weight }

def exampleTree : WeightedTree := mkWeightedTree 2

#eval! addWeight exampleTree 10 (by decide)
