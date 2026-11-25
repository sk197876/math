(** Federer (1969), 4.1.10, p. 364: a closed current has
    no boundary contribution to its cone formula. The supporting
    zero-pushforward law follows directly from the original action
    law of 4.1.7, p. 359, for arbitrary currents and open domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentProperSupport CurrentPushforwardUP
  CurrentPushforwardExistence CurrentPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_pushforward_of_zero]: the original
    proper pushforward sends the zero current to zero, supporting
    the closed-current deductions in Federer 4.1.10, p. 364.
    The statement permits every original properness proof. *)
Theorem current_pushforward_of_zero (R : realType) (h2 : (1+1:R)!=0)
    (v n j : nat) (U : set (R_n R v)) (V : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV : forall y, V y -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V y)
    (f : R_n R v -> R_n R n) (hImage : forall x, U x -> V (f x))
    (hf : norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f)
    (T : @current_space R h2 v U hU j)
    (hProper : @is_current_proper_on_support R h2 v n j U hU V T f hImage) :
  T=0 -> @CurrentPushforward.value R h2 v n j U V hU hV T f hImage hf hProper=0.
Proof.
move=> hZero; apply: current_values_extensional => psi.
have [alpha hAlpha] := @current_pushforward_test_replacement_exists R h2 v n j
  U V hU hV T f hImage hf hProper psi.
rewrite (@CurrentPushforward.laws R h2 v n j U V hU hV T f hImage hf hProper psi alpha hAlpha).
by rewrite hZero (linear0 (@current_value R h2 v U hU j)) hom_zeroE
  (linear0 (@current_value R h2 n V hV j)) hom_zeroE.
Qed.
