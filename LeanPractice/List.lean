import Init.Prelude
import Mathlib.Order.Defs.LinearOrder

variable {A : Type}
variable {x y z : A}
variable {a a' b b' c c' lacc : List A}

open List hiding reverse reverse_cons perm_middle insert merge mergeSort

def cat (a b : List A) : List A := match a with
  | nil => b
  | cons x xs => cons x (cat xs b)

infixr:5 " <> " => cat

@[simp]
theorem cat_nil_l : (nil <> a) = a := by rfl

@[simp]
theorem cat_nil_r : (a <> nil) = a := by
  induction a
  case nil =>
    apply Eq.refl
  case cons x xs ind =>
    unfold cat
    congr

theorem length_cat : length (cat a b) = length a + length b := by
  induction a
  next =>
    unfold cat
    simp
  next xs x h =>
    unfold cat
    conv in length (cons _ _) => unfold length
    rw [h]
    conv in length (cons _ _) => unfold length
    rw [Nat.add_assoc, Nat.add_assoc]
    conv in (1 + length b) => rw [Nat.add_comm]

theorem length_cat_commut : length (cat a b) = length (cat b a) := by
  rw [length_cat, Nat.add_comm, Eq.symm length_cat]

theorem cat_assoc : cat (cat a b) c = cat a (cat b c) := by
  induction a
  next =>
   repeat rw [cat_nil_l]
  next x xs ind =>
    repeat rw [cat]
    congr

@[reducible]
def reverseGo (acc : List A) (d : List A) : List A := match d with
   | nil  => acc
   | x :: xs => reverseGo (x :: acc) xs

@[reducible]
def reverse : List A -> List A :=
 reverseGo nil

theorem reverseGo_cons : reverseGo lacc (x :: a) = (reverse a <> x :: lacc) := by
  induction a generalizing x lacc
  case nil =>
    rfl
  case cons y xs ind =>
    rw [reverseGo, ind, reverse, ind, cat_assoc]
    rfl

theorem reverse_cons : reverse (x :: a) = cat (reverse a) [x] := by
  apply reverseGo_cons

theorem length_reverse : length a = length (reverse a) := by
  induction a
  case nil =>
    rfl
  case cons x xs ind =>
    rw [length, ind, reverse_cons, length_cat, length, length, Nat.add_zero, Nat.add_comm]

theorem reverse_cat : reverse (cat a b) = cat (reverse b) (reverse a) := by
  induction a
  case nil =>
    rw [reverse, reverseGo, cat, cat_nil_r]
  case cons x xs ind =>
    rw [cat, reverse_cons, ind, reverse_cons, cat_assoc]

theorem reverse_reverse : reverse (reverse a) = a := by
  induction a
  case nil =>
    rfl
  case cons x xs ind =>
    rw [reverse_cons, reverse_cat, ind]
    rfl

theorem perm_middle {x : A} {a b : List A} : (a <> x :: b) ~ (x :: (a <> b)) := match a, b with
  | [], _ => by
    simp
  | y :: c, d => by
    rw [cat]
    apply Perm.symm
    calc x :: (y :: c <> d)
         _ ~ y :: (x :: c <> d) := by apply Perm.swap
         _ ~ y :: (c <> x :: d) := by
             refine (Perm.cons _ ?_)
             exact (Perm.symm perm_middle)
         _ ~ ((y :: c) <> (x :: d)) := by
           rw [cat]

theorem perm_last {x : A} {a : List A} : (a <> [x]) ~ (x :: a) := by
  have h := perm_middle (x := x) (a := a) (b := nil)
  simp at h
  exact h

theorem reverse_perm : Perm a (reverse a) := by
  induction a
  case nil =>
    simp
  case cons x xs ind =>
    apply Perm.symm
    calc reverse (x :: xs)
     _ ~ (reverse xs <> [x]) := by rw [reverse_cons]
     _ ~ x :: reverse xs := by apply perm_last
     _ ~ x :: xs := by
       apply Perm.cons
       apply (Perm.symm ind)

@[reducible, simp]
def All (p : A -> Prop) : List A -> Prop
  | [] => True
  | x :: xs => p x ∧ All p xs

@[reducible, simp]
def Sorted [le : LE A] : List A -> Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ Sorted (y :: xs)

def sortedTail [LE A] (p : Sorted (x :: a)) : Sorted a :=
  match a with
  | [] => True.intro
  | _ :: _ => match p with
    | And.intro _ k => k

@[reducible]
def myinsert [le : LE A] [ord : DecidableLE A] (new : A) (a : List A) (sorted : Sorted a) : List A :=
  match a with
    | [] => [new]
    | x :: xs => match ord new x with
      | isTrue _ => new :: x :: xs
      | isFalse _ => x :: myinsert new xs (sortedTail sorted)

theorem sorted_le_all [Preorder A] {a : List A}
  {s : Sorted (x :: a)}
  (mem : y ∈ x :: a)
  : x ≤ y := by
  induction a generalizing x
  case nil =>
    simp at mem
    rw [mem]
  case cons w ys ih =>
    simp at mem s
    rcases s with ⟨xw, sor⟩
    rcases mem with eq | eq | eq
    case inl =>
      rw [eq]
    case inr.inl =>
      rw [eq]
      assumption
    case intro.inr.inr =>
      have wy : w ≤ y := by
        apply ih
        assumption
        case mem m =>
          right
          assumption
      next =>
        apply Preorder.le_trans
        apply xw
        assumption

lemma myinsert_head [LinearOrder A] [cmp : DecidableLE A] {a : List A} {new : A}
  (s : Sorted a)
  : ∃ newHead : A, ∃ l : List A,
    newHead :: l = myinsert new a s ∧
    ((new = newHead ∧ l = a) ∨ newHead ∈ a) := by
  cases a; simp
  case cons head tail =>
    unfold myinsert
    cases cmp new head; simp
    case isFalse hfalse =>
      exists head, (myinsert new tail (sortedTail s))
      simp
    case isTrue =>
      exists new, (head :: tail)
      simp

theorem insertSorted
  [LinearOrder A] [cmp : DecidableLE A]
  (a : List A) (p : Sorted a) {new : A} : Sorted (myinsert new a p) := by
  induction a
  case nil =>
    simp
  case cons x xs ind =>
    obtain ⟨newHead, newTail, ⟨eq, or⟩⟩ := myinsert_head (new := new) (sortedTail p)
    specialize ind (sortedTail p)
    unfold myinsert
    cases cmp new x; simp
    next neq =>
      rw [<- eq] at *
      cases or; simp
      case inl h =>
       obtain ⟨eq1, newTailxs⟩ := h
       rw [<- eq1] at ind ⊢
       constructor
       exact le_of_not_ge neq
       assumption
      case inr mem =>
       simp
       constructor
       apply sorted_le_all (s := p) (mem_cons_of_mem x mem)
       apply ind
    next h =>
      constructor
      assumption
      assumption

@[reducible]
def insertionSort [LinearOrder A] (a : List A) : List A :=
  let rec @[reducible] go (acc : List A) (s : Sorted acc) (rem : List A) : List A := match rem with
         | [] => acc
         | cons x xs => go (myinsert x acc s) (insertSorted acc s) xs
  go [] True.intro a

theorem insertionSort_sorted [LinearOrder A] (a : List A) :
 Sorted (insertionSort a) := by
   rw [insertionSort]
   have goSorted (acc : List A) (p : Sorted acc) (l : List A) : Sorted (insertionSort.go acc p l) := by
         induction l generalizing acc
         case nil => assumption
         case cons b bs ih => apply ih (myinsert b acc p) (insertSorted acc p)

   apply goSorted

theorem insertPerm [le : LE A] [ord : DecidableLE A]
  (p : Sorted a)
  : Perm (x :: a) (myinsert x a p) := by
        induction a generalizing x
        case nil => simp
        case cons y ys ih =>
          unfold myinsert
          cases ord x y
          case isFalse =>
            have pp := Perm.cons y (ih (x := x) (sortedTail p))
            calc x :: y :: ys
              _ ~ y :: x :: ys := by apply Perm.swap
              _ ~ y :: (myinsert x ys (sortedTail p)) := pp
          case isTrue => simp

theorem perm_cat_left {a a' b : List A} (pa : a ~ a') : (a <> b) ~ (a' <> b) := by
  induction b
  case nil =>
    iterate 2 (rw [cat_nil_r])
    assumption
  case cons x xs ih =>
    calc (a <> x :: xs)
    _ ~ x :: (a <> xs) := by apply perm_middle
    _ ~ x :: (a' <> xs) := by exact Perm.cons x ih
    _ ~ (a' <> x :: xs) := by apply (Perm.symm perm_middle)

theorem perm_cat_right {a b b' : List A} (pb : b ~ b') : (a <> b) ~ (a <> b') := by
  induction a
  case nil =>
    simp
    assumption
  case cons x xs ih =>
    apply Perm.cons
    assumption


theorem perm_cat {a a' b b' : List A} (pa : a ~ a') (pb : b ~ b') : (a <> b) ~ (a' <> b') := by
    calc (a <> b)
    _ ~ (a' <> b) := by apply (perm_cat_left pa)
    _ ~ (a' <> b') := by apply (perm_cat_right pb)

theorem insertionSort_perm [LinearOrder A] (a : List A) :
   a ~ insertionSort a := by
   rw [insertionSort]
   have goLemma (acc : List A) (s : Sorted acc) (rem : List A) :
        (rem <> acc) ~ insertionSort.go acc s rem := by
        induction rem generalizing acc
        case nil => simp
        case cons y ys ih =>
          unfold insertionSort.go
          apply Perm.symm
          have sacc : Sorted (myinsert y acc s) := insertSorted acc s
          calc insertionSort.go (myinsert y acc s) sacc ys
            _ ~ (ys <> myinsert y acc s) := Perm.symm (ih (myinsert y acc s) sacc)
            _ ~ (ys <> y :: acc) := by
                                  apply perm_cat_right
                                  apply (Perm.symm (insertPerm s))
            _ ~ (y :: (ys <> acc)) := by apply perm_middle

   have l := goLemma [] True.intro a
   rw [cat_nil_r] at l
   apply l

structure SortingAlgorithm (A : Type) [LinearOrder A] where
  sort : List A -> List A
  sort_perm : ∀ (l : List A), Perm l (sort l)
  sort_sorted : ∀ (l : List A), Sorted (sort l)

def insertionSortAlgorithm [LinearOrder A] : SortingAlgorithm A :=
  {
  sort := insertionSort ,
  sort_perm := insertionSort_perm ,
  sort_sorted := insertionSort_sorted
  : SortingAlgorithm A
  }

def split [LinearOrder A] (pivot : A) (l : List A) : List A × List A
  := partition (fun y => y ≤ pivot) l

-- theorem split_partition {A : Type} [LinearOrder A] (x : A) (l : List A) :
--     let (left, right) := split x l
--     (∀ y ∈ left, y ≤ x) ∧ (∀ y ∈ right, x < y) := by
--     unfold split
--     rw [partition_eq_filter_filter]
--     constructor <;> simp

@[reducible]
def merge_helper (cmp : A -> A -> Bool) (a b : List A) : List A := match a, b with
  | [], b => b
  | a, [] => a
  | (x :: xs), (y :: ys) => if cmp x y
    then x :: merge_helper cmp xs (y :: ys)
    else y :: merge_helper cmp (x :: xs) ys

@[reducible]
def merge [LE A] [DecidableLE A] (a b : List A) : List A := match a, b with
  | [], b => b
  | a, [] => a
  | (x :: xs), (y :: ys) => if x ≤ y
    then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys

-- TODO simplify
def merge_sorted [LinearOrder A] (sa : Sorted a) (sb : Sorted b) : Sorted (merge a b) := by
  induction a generalizing b
  case nil =>
    rw [merge]
    assumption
  case cons x xs ih =>
    induction b generalizing xs
    case nil =>
      unfold merge
      assumption
    case cons y ys ih2 =>
      unfold merge
      split
      case isTrue h =>
        specialize @ih (y :: ys) (sortedTail sa)
        cases xs
        case nil =>
          unfold merge at *
          unfold Sorted
          exact ⟨h, sb⟩
        case cons u us =>
          unfold merge at *
          split
          case isTrue =>
            simp [*] at ih
            simp [*]
          case isFalse h2 =>
            simp [*] at ih
            exact ⟨h, ih⟩
      case isFalse h =>
        have h1 : y ≤ x := le_of_not_ge h
        cases ys
        case nil =>
          unfold merge
          exact  ⟨h1, sa⟩
        case cons z zs =>
          unfold merge
          split
          case isTrue h2 =>
            specialize ih2 xs ih sa (sortedTail sb)
            constructor
            assumption
            unfold merge at ih2
            simp [*] at ih2
            assumption
          case isFalse h2 =>
            have h2' : z < x := lt_of_not_ge h2
            specialize ih2 xs ih sa (sortedTail sb)
            unfold merge at ih2
            simp [*] at ih2
            constructor
            cases sb
            assumption
            assumption

lemma merge_perm [LinearOrder A]
   : (merge a b) ~ (a <> b) := by
   apply Perm.symm
   induction a generalizing b
   case nil =>
     unfold merge
     simp
   case cons x xs ih =>
     induction b
     case nil =>
       simp
       unfold merge
       apply Perm.refl
     case cons y ys ih2 =>
       unfold merge
       split
       case isTrue x_le_y =>
         simp [cat, ih]
       case isFalse x_ge_y =>
         calc (x :: xs <> y :: ys)
          _ ~ y :: (x :: xs <> ys) := by apply perm_middle
         apply Perm.cons
         apply ih2

theorem filter_size (f : A -> Bool) (xs : List A)
  : sizeOf (filter f xs) ≤ sizeOf xs := by
  induction xs
  case nil => simp
  case cons y ys ih =>
    unfold filter
    split
    case h_1 =>
      simp
      apply ih
    case h_2 =>
      simp
      calc sizeOf (filter f ys)
       _ ≤ sizeOf ys := ih
       _ ≤ 1 + sizeOf ys := by apply Nat.le_add_left

theorem split_size [LinearOrder A] (x : A) (xs : List A) :
  let (l, r) := split x xs
  (sizeOf l ≤ sizeOf xs ∧ sizeOf r ≤ sizeOf xs) := by
  unfold split
  rw [partition_eq_filter_filter]
  simp
  constructor <;> apply filter_size

def mergeSort [LinearOrder A] (d : List A) : List A :=
  match d with
   | [] => []
   | (x :: xs) =>
        match _eq : split x xs with
         | (l, r) => merge (mergeSort l) (x :: (mergeSort r))
        decreasing_by
        iterate 2 {
        have prf2 := split_size x xs
        rw [_eq] at prf2
        simp
        omega
        }

theorem filter_perm (f : A -> Bool) (a : List A)
  : ((filter f a) <> (filter (not ∘ f) a)) ~ a
  := by
  induction a
  case nil => simp
  case cons x xs ih =>
    unfold filter Function.comp
    split
    next isTrue =>
      rw [isTrue]
      simp
      apply Perm.cons
      apply ih
    next isFalse =>
      rw [isFalse]
      simp
      calc (filter f xs <> x :: filter (fun x ↦ !f x) xs)
      _ ~ x :: (filter f xs <> filter (fun x ↦ !f x) xs) := by apply perm_middle
      _ ~ x :: xs := by
        apply Perm.cons
        exact ih

theorem mergeSort_perm [LinearOrder A] (d : List A) :
  d ~ mergeSort d := by
  apply WellFounded.induction sizeOfWFRel.wf d
  intro ls ih
  cases ls
  case nil => rw [mergeSort]
  case cons x xs =>
    unfold mergeSort split
    match eq : partition (fun y => decide (y ≤ x)) xs with
     | (pl, pr) =>
       rw [<- eq, partition_eq_filter_filter]
       simp
       apply Perm.symm
       let ih2 {f : A -> Bool} : filter f xs ~ mergeSort (filter f xs) := by
         apply ih (filter f xs)
         calc sizeOf (filter f xs)
          _ ≤ sizeOf xs := by exact filter_size f xs
          _ < sizeOf (x :: xs) := by simp

       calc merge (mergeSort (filter (fun y ↦ decide (y ≤ x)) xs)) (x :: mergeSort (filter (not ∘ fun y ↦ decide (y ≤ x)) xs))
         _ ~ ((mergeSort (filter (fun y ↦ decide (y ≤ x)) xs)) <> (x :: mergeSort (filter (not ∘ fun y ↦ decide (y ≤ x)) xs))) :=
                   by apply merge_perm
         _ ~ x :: ((mergeSort (filter (fun y ↦ decide (y ≤ x)) xs)) <>
                   (mergeSort (filter (not ∘ fun y ↦ decide (y ≤ x)) xs))) :=
                   by exact perm_middle
         _ ~ x :: ((filter (fun y ↦ decide (y ≤ x)) xs) <>
                   (filter (not ∘ fun y ↦ decide (y ≤ x)) xs)) := by
                   apply Perm.cons
                   apply Perm.symm (perm_cat ih2 ih2)
         _ ~ x :: xs := by
                   apply Perm.cons
                   apply filter_perm

theorem perm_mem (p : a ~ b) (m : x ∈ a) : x ∈ b := by
  induction p
  assumption
  case cons y l1 l2 p ih =>
   rcases m
   simp
   next h1 =>
     right
     apply ih
     assumption
  case swap x1 x2 l3 =>
    rcases m
    right
    apply Mem.head
    case tail m =>
      rcases m
      apply Mem.head
      case tail m => right; right; assumption
  case trans h2 h3 =>
    apply h3
    apply h2
    assumption

theorem mergeSort_sorted [LinearOrder A] (d : List A)
  : Sorted (mergeSort d) := by
  apply WellFounded.induction sizeOfWFRel.wf d
  intros a ih
  rw [WellFoundedRelation.rel] at ih
  unfold mergeSort
  cases a; simp
  case cons x xs =>
    simp
    unfold split
    rw [partition_eq_filter_filter]
    simp
    have h1 : Sorted (mergeSort (filter (fun y ↦ decide (y ≤ x)) xs)) := by
      apply ih
      have s1 : sizeOf (filter (fun y ↦ decide (y ≤ x)) xs) < sizeOf (x :: xs) :=
        calc sizeOf (filter (fun y ↦ decide (y ≤ x)) xs)
          _ ≤ sizeOf xs := by apply filter_size
          _ < sizeOf (x :: xs) := by simp
      apply s1
    have h2 : Sorted (x :: (mergeSort (filter (not ∘ fun y ↦ decide (y ≤ x)) xs))) := by
      have h21 : Sorted (mergeSort (filter (not ∘ fun y ↦ decide (y ≤ x)) xs)) := by
        apply ih
        calc sizeOf (filter _ xs)
          _ ≤ sizeOf xs := by apply filter_size
          _ < sizeOf (x :: xs) := by simp
      cases c : mergeSort (filter (not ∘ fun y ↦ decide (y ≤ x)) xs)
      simp
      case cons z zx =>
        rw [c] at h21
        constructor
        have zx : x < z := by
          have zmem : z ∈ mergeSort (filter (not ∘ fun y ↦ decide (y ≤ x)) xs) := by
            rw [c]
            simp
          have zfilter : z ∈ filter (not ∘ fun y ↦ decide (y ≤ x)) xs := perm_mem (Perm.symm (mergeSort_perm _)) zmem
          have xlez := And.right (Iff.mp mem_filter zfilter)
          simp at xlez
          assumption
        exact le_of_lt zx
        assumption
    apply merge_sorted
    assumption
    assumption
