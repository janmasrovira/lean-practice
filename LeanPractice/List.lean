variable {A : Type}
variable {x y z : A}
variable {a b c lacc : List A}

open List hiding reverse

def cat (a b : List A) : List A := match a with
  | nil => b
  | cons x xs => cons x (cat xs b)

theorem cat_nil_l : cat nil a = a := by rfl

theorem cat_nil_r : cat a nil = a := by
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

def reverseGo (acc : List A) (d : List A) : List A := match d with
   | nil  => acc
   | cons x xs => reverseGo (cons x acc) xs

def reverse : List A -> List A :=
 reverseGo nil

infixr:5 " ⟨⟩ " => cat

theorem reverseGo_cons : reverseGo lacc (cons x a) = cat (reverse a) (cons x lacc) := by
  induction a generalizing x lacc
  case nil =>
    rfl
  case cons y xs ind =>
    rw [reverseGo, ind, reverse, ind, cat_assoc]
    rfl

-- theorem reverse_cons : reverse (cons x a) = cat (reverse a) (cons x nil) := by
--   apply reverseGo_cons

-- theorem length_reverse : length a = length (reverse a) := by
--   induction a
--   case nil =>
--     rfl
--   case cons x xs ind =>
--     rw [length, ind, reverse_cons, length_cat, length, length, Nat.add_zero, Nat.add_comm]

-- theorem reverse_cat : reverse (cat a b) = cat (reverse b) (reverse a) := by
--   induction a
--   case nil =>
--     rw [reverse, reverseGo, cat, cat_nil_r]
--   case cons x xs ind =>
--     rw [cat, reverse_cons, ind, reverse_cons, cat_assoc]

-- theorem reverse_reverse : reverse (reverse a) = a := by
--   induction a
--   case nil =>
--     rfl
--   case cons x xs ind =>
--     rw [reverse_cons, reverse_cat, ind]
--     rfl
