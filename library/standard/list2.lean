----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Parikshit Khanna. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Parikshit Khanna, Jeremy Avigad
----------------------------------------------------------------------------------------------------

-- Theory list2
-- ============
--
-- More basic properties of lists.

import macros
import tactic
import nat
import list

using nat
unary_nat

namespace list

axiom sorry {P : Bool} : P

theorem insert_cons_ge (n m : ℕ) (H : m ≤ n) (l : list ℕ) : insert n (cons m l) = cons m (insert n l)
:= trans (insert_cons n m l) (imp_if_eq H _ _)

theorem insert_cons_lt (n m : ℕ) (H : n < m) (l : list ℕ) : insert n (cons m l) = cons n (cons m l)
:= trans (insert_cons n m l) (not_imp_if_eq (lt_imp_not_ge H) _ _)

-- temporary, until Lean 2.0
theorem ge_iff_le (n m : ℕ) : (n ≥ m) = (m ≤ n) := refl _
theorem gt_iff_lt (n m : ℕ) : (n > m) = (m < n) := refl _

add_rewrite insert_cons_ge insert_cons_lt ge_iff_le gt_iff_lt

--    (if n ≥ m then cons m (insert n l) else cons n (cons m l))


theorem insert_comm_aux (x y : ℕ) (H : x < y) (l : list ℕ) : insert x (insert y l) = insert y (insert x l)
:= 
  list_induction_on l 
    (show insert x (insert y nil) = insert y (insert x nil), from (by simp) (lt_imp_le H))
    (take z l, 
      assume IH : insert x (insert y l) = insert y (insert x l),
      show insert x (insert y (cons z l)) = insert y (insert x (cons z l)), from 
        or_elim (le_or_gt z y)
          (assume H1 : z ≤ y, 
            or_elim (le_or_gt z x)
              (assume H2 : z ≤ x, by simp)
              (assume H2 : x < z, 
                have H3 : x ≤ y, from lt_imp_le H,
                by simp))
          (assume H1 : y < z, 
            have H2 : x < z, from lt_trans H H1,
            have H3 : x ≤ y, from lt_imp_le H,
            by simp))

theorem insert_comm (x y : ℕ) (l : list ℕ) : insert x (insert y l) = insert y (insert x l)
:= 
  or_elim (trichotomy x y)
    (assume H, insert_comm_aux x y H l)
    (assume H, or_elim H
      (assume H1, subst (refl _) H1)
      (assume H1, symm (insert_comm_aux y x H1 l))) 








-- definition map {T : Type} {S : Type} (P : T → S) (x0 : S) : list T → list S
-- := list_rec (cons x0 nil) (fun x l b, cons (P x) b)

-- definition foldr {T : Type} {S : Type} (f : T → T → T) (x0 : T) : list T → T
-- := list_rec x0 (fun x l b,f x b)

-- -- l = x [a b c d]
-- -- b =  f(c f( b (f a d))))      f( a (f b (f c d)))  f (f (f a b) c) d
-- -- r =  f (c f(b f(a (f x d))))  f  a  f  b  f c d    f  ( f (f  ( f x a) b) c) d

-- definition last {T : Type} (x0 : T) (l : list T) : T
-- := head x0 (reverse l)

-- theorem find_insert (x y : ℕ) (l : list ℕ) : find x (insert y (asort l)) =  (if y ≥ x then find x (asort l) else succ (find x (asort l)))
-- :=
--  by_cases _
--    (assume H : y ≥ x,
--     list_induction_on l
--      ((by simp) (asort_nil) (insert_nil y) (find_cons x y nil) 
--      (find_nil x))
--    (take z l,
--     assume IH : find x (insert y (asort l)) =  (if y ≥ x then find x l else succ (find x l)),
--        by_cases _
--          (assume H1 : y ≥ z,
--          by_cases _
--           (assume H2 :  z ≥ x,
--           (by simp) (asort_cons z l) (insert_cons _ _ l) (find_cons _ _ l))
--           (assume H2 : ¬ z ≥ x,
--           (by simp) (insert_cons _ _ l) (find_cons _ _ l)))
--         (assume H1 : ¬ y ≥ z,
--           by_cases _
--           (assume H2 : z ≥ x,
--            (by simp) (insert_cons _ _ l) (find_cons _ _ l))
--           (assume H2 : ¬ z ≥ x,
--            (by simp) (insert_cons _ _ l) (find_cons _ _ l))))
--    (assume H : ¬ y ≥ x,
--      list_induction_on l
--      ((by simp) (asort_nil) (insert_nil y) (find_cons x y nil) 
--      (find_nil x))
--    (take z l,
--     assume IH : find x (insert y (asort l)) =  (if y ≥ x then find x l else succ (find x l)),
--        by_cases _
--          (assume H1 : y ≥ z,
--          by_cases _
--           (assume H2 :  z ≥ x,
--           (by simp) (asort_cons z l) (insert_cons _ _ l) (find_cons _ _ l))
--           (assume H2 : ¬ z ≥ x,
--           (by simp) (insert_cons _ _ l) (find_cons _ _ l)))
--         (assume H1 : ¬ y ≥ z,
--           by_cases _
--           (assume H2 : z ≥ x,
--            (by simp) (insert_cons _ _ l) (find_cons _ _ l))
--           (assume H2 : ¬ z ≥ x,
--            (by simp) (insert_cons _ _ l) (find_cons _ _ l))))))

theorem find_insert (x y : ℕ) (l : list ℕ) :
 mem x l → (find x (insert y (asort l)) =  (if y ≥ x then find x (asort l) else succ (find x (asort l))))
:= list_induction_on l
   (assume H1 : mem x nil,
    show  find x (insert y (asort nil)) =  (if y ≥ x then find x (asort nil) else succ (find x (asort nil))),
    from false_elim _ ((iff_elim_left (mem_nil x)) H1)
   ) (take z l,
      sorry)
