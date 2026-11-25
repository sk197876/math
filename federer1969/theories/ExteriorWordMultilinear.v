(** Federer (1969), 3.2.28(2), printed p. 264: the exterior
    power map is polynomial. This supporting algebra expresses
    its coefficient as the actual ordered exterior word, using
    the multilinearity of 1.3.1 and 1.4.1, pp. 13–17. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorFamilyUP FamilyUpdate WordEvaluation
  PowerWords ExteriorSealed ExteriorAlgebra ExteriorGrading
  GradedComponents FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_ordered_word_multilinear]: the ordered
    exterior word is linear in each factor, 1.3.1 and 1.4.1,
    pp. 13–17. Supporting coefficient law for the polynomial
    Q in Federer 3.2.28(2), p. 264, including the empty word. *)
Lemma exterior_ordered_word_multilinear (K:fieldType) (V:lmodType K) m:
  multilinear (fun u:{ffun 'I_m->V}=>e_lambda u (ord_tuple m)).
Proof.
have hw:=@multilinear_words_power K V (exterior_space V)
  (@exterior_word K V) m
  (@word_eval_multilinear K V (exterior_algebra V) (exterior_generator_map V)).
move=>u i a x y; apply:val_inj.
change (component_val (e_lambda (family_with (i:=i) u (a *: x+y)) (ord_tuple m))=
  component_val (a *:e_lambda (family_with (i:=i) u x) (ord_tuple m)+
    e_lambda (family_with (i:=i) u y) (ord_tuple m))).
rewrite linearD linearZ !e_lambdaE !val_ord_tuple.
exact:(hw u i a x y).
Qed.
