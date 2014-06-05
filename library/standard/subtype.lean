-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import macros
import kernel

-- Simulate "subtypes" using Sigma types and proof irrelevance
definition subtype (A : Type) (P : A → Bool) := sig x, P x

namespace subtype
definition rep {A : Type} {P : A → Bool} (a : subtype A P) : A
:= proj1 a

definition abst {A : Type} {P : A → Bool} (r : A) (H : inhabited (subtype A P)) : subtype A P
:= ε H (λ a, rep a = r)

theorem subtype_inhabited {A : Type} {P : A → Bool} (a : A) (H : P a) : inhabited (subtype A P)
:= inhabited_intro (pair a H)

theorem subtype_inhabited_exists {A : Type} {P : A → Bool} (H : ∃ x, P x) : inhabited (subtype A P)
:= obtain (w : A) (Hw : P w), from H,
     inhabited_intro (pair w Hw)

theorem P_rep {A : Type} {P : A → Bool} (a : subtype A P) : P (rep a)
:= proj2 a

theorem rep_inj {A : Type} {P : A → Bool} {a b : subtype A P} (H : rep a = rep b) : a = b
:= pairext _ _ H (hproof_irrel (proj2 a) (proj2 b))

theorem ex_abst {A : Type} {P : A → Bool} {r : A} (H : P r) : ∃ a, rep a = r
:= exists_intro (pair r H) (refl r)

theorem abst_rep {A : Type} {P : A → Bool} (H : inhabited (subtype A P)) (a : subtype A P)
                 : abst (rep a) H = a
:= let s1 : rep (abst (rep a) H) = rep a  :=
                @eps_ax (subtype A P) H (λ x, rep x = rep a) a (refl (rep a))
   in rep_inj s1

theorem rep_abst {A : Type} {P : A → Bool} (H : inhabited (subtype A P)) : ∀ r, P r → rep (abst r H) = r
:= take r, assume Hl : P r,
     @eps_ax (subtype A P) H (λ x, rep x = r) (pair r Hl) (refl r)

theorem abst_inj {A : Type} {P : A → Bool} (H : inhabited (subtype A P)) {r r' : A} :
                 P r → P r' → abst r H = abst r' H → r = r'
:= assume Hr Hr' Heq,
      calc r    = rep (abst r  H)  :  symm (rep_abst H r Hr)
           ...  = rep (abst r' H)  :  { Heq }
           ...  = r'               :  rep_abst H r' Hr'

theorem ex_rep {A : Type} {P : A → Bool} (H : inhabited (subtype A P)) :
               ∀ a, ∃ r, abst r H = a ∧ P r
:= take a, exists_intro (rep a) (and_intro (abst_rep H a) (proj2 a))

set_opaque rep     true
set_opaque abst    true
end -- namespace subtype
set_opaque subtype true
