import Init.Prelude
import Mathlib.Order.Defs.LinearOrder

variable {A : Type}
variable {x y z : A}
variable {a a' b b' c c' lacc : List A}

open List hiding reverse reverse_cons perm_middle insert

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


theorem reverseGo_cons : reverseGo lacc (x :: a) = cat (reverse a) (x :: lacc) := by
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
    | (x :: xs) => match ord new x with
      | isTrue _ => new :: x :: xs
      | isFalse _ => x :: myinsert new xs (sortedTail sorted)

theorem sorted_le_all [Preorder A] {a : List A} (p : Sorted (x :: a))
  : All (λ e => x ≤ e) a := by
  induction a
  case nil => simp
  case cons y ys ih =>
    simp at p
    rcases p with ⟨h1, h2⟩
    simp
    refine (And.intro h1 ?_)
    apply ih
    cases ys
    case intro.nil => simp
    case intro.cons z zs =>
      rcases h2 with ⟨yz, sortedz⟩
      simp
      constructor
      case intro.left =>
        exact Preorder.le_trans x y z h1 yz
      case intro.right =>
        assumption

theorem insertSorted
  [ord : LinearOrder A] (a : List A)
  (p : Sorted a)
  {new : A} : Sorted (myinsert new a p) := by
  induction a
  case nil =>
    simp
  case cons x xs h =>
    unfold myinsert
    cases le_total new x
    case inl le =>
      cases instDecidableLe_mathlib new x
      case isFalse => contradiction
      case isTrue =>
        simp
        exact (And.intro le p)
    case inr le =>
      cases instDecidableLe_mathlib new x
      case isTrue t =>
        simp
        exact (And.intro t p)
      case isFalse =>
        simp
        have sTail := h (sortedTail p)
        let tail := myinsert new xs (sortedTail p)
        cases xs
        case nil =>
          simp
          assumption
        case cons hd tl =>
          unfold myinsert
          cases le_total new hd
          case inl =>
            cases instDecidableLe_mathlib new hd
            case isFalse _ => contradiction
            case isTrue newhd =>
              simp
              exact (And.intro le (And.intro newhd (sortedTail p)))
          case inr ww =>
            cases instDecidableLe_mathlib new hd
            case isTrue newhd =>
              simp
              exact (And.intro le (And.intro newhd (sortedTail p)))
            case isFalse newhd =>
              simp
              rcases p with ⟨p1, _⟩
              refine (And.intro p1 ?_)


               -- simp [myinsert] at sTail
