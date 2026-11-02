(** Supporting compact inner approximation for Federer (1969), 2.10.5(2), p.
    173, projection-volume continuity. The actual Euclidean Lebesgue measure
    is Haar by 2.7.16(1), p. 134, hence Radon by 2.7.14, p. 131. Its closed
    unit cube of volume one supplies the nonvanishing condition of the
    corrected local Radon theorem. The compact inner bound is the defining
    law of 2.2.5, p. 62. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanAdditiveGroup
  EuclideanLebesgueDimensions EuclideanLebesgueHaar HaarIntegralUP CovariantIntegralUP
  CovariantMeasureRadon RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_lebesgue_radon]: supporting
    Radon consequence of the Haar identification
    in Federer 2.7.16(1), p. 134, used for
    the projected-volume continuity of 2.10.5(2),
    p. 173. The actual measure is nonzero
    on its compact closed unit cube, including
    the existing degree-zero convention. *)
Theorem euclidean_lebesgue_radon (R : realType) (n : nat) :
  is_radon_measure (@euclidean_lebesgue_measure R n).
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have [nu [hnu hm hrep hreg]] := @euclidean_lebesgue_left_haar R n.
have hcov : is_left_covariant_measure (fun x y : E => (x+y)%R)
    (fun _ => 1%R) (@euclidean_lebesgue_measure R n).
  exists nu; split.
  - exact: nonzero_invariant_integral_monotone hnu.
  - exact: covariant_integral_law (nonzero_invariant_integral_invariant hnu).
  - exact hm.
  - exact hrep.
  - exact hreg.
apply: (@left_covariant_measure_radon R E (fun x y : E => (x+y)%R)
  (fun x : E => (-x)%R) (0:E)%R (@euclidean_additive_lch_group R n)
  (fun _ => 1%R) (@euclidean_lebesgue_measure R n) hcov).
left; have [hC hv] := @euclidean_unit_closed_cube R n.
exists [set x : E | forall i, (0<=x i<=1)%R]; split=> //.
by rewrite hv; exact/eqP/oner_neq0.
Qed.

(** Source for [euclidean_open_compact_inner_volume]:
    supporting strict compact inner bound in the
    continuity argument for Federer 2.10.5(2),
    p. 173, from the Radon definition 2.2.5,
    p. 62. Infinite open-set volumes and empty
    compact approximants are permitted. *)
Lemma euclidean_open_compact_inner_volume (R : realType) (m : nat)
    (U : set (inner_metric_space (@euclidean_inner_productP R m))) (b : R) :
  open U -> b%:E<euclidean_lebesgue_measure m U ->
  exists K, compact K /\ K `<=` U /\ b%:E<euclidean_lebesgue_measure m K.
Proof.
move=> hU hb; case: (pselect (exists K, compact K /\ K `<=` U /\
    b%:E<euclidean_lebesgue_measure m K))=> [//|hno].
exfalso; have hbound : euclidean_lebesgue_measure m U<=b%:E.
  apply: (radon_inner_least (@euclidean_lebesgue_radon R m) hU)=> K hK hKU.
  rewrite leNgt; apply/negP=> hlt; apply: hno; by exists K.
by move: hb; rewrite ltNge hbound.
Qed.
