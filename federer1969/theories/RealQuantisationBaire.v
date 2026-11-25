(** Federer (1969), 2.2.15, p. 71: each integer- cell approximant h_i is
    Baire, being the sum over j of (j/i) times the cell characteristic
    function. The countable sum is justified by finite partial sums that are
    eventually constant at each source point. No external infinite-series or
    measurable-function approximation theorem is used. *)
From mathcomp Require Import all_boot all_algebra ssrint boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground RealIntegerCells RealQuantisationUP
  BorelFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed
  BorelCharacteristicBaire BaireFunctions BaireRealAlgebra IntegerCharacteristicSums
  PointwiseEventuallyConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [borel_real_quantisation_baire]: direct h_i
    Baire assertion in Federer 2.2.15, p. 71. The
    integer cells are Borel, their characteristic functions are
    Baire, and exactly one cell contains each point. The
    approximant is supplied only through its abstract laws. *)
Theorem borel_real_quantisation_baire (R : realType) (X : metricType R)
    (f q : X -> real_line_metric R) k :
  is_borel_function f -> is_real_quantisation f q k -> is_baire_function q.
Proof.
move=> hf hq.
pose A j := real_integer_cell f k j.
pose g j : X -> real_line_metric R := @CharacteristicFunction.value R X (A j).
pose c (j : int) : R := j%:~R / (k.+1)%:R.
pose u := integer_characteristic_term c g.
have hg j : is_characteristic_function (A j) (g j) := @CharacteristicFunction.laws R X (A j).
have hgb j : is_baire_function (g j).
  apply: (@borel_characteristic_baire R X (A j) (g j)); last exact: hg.
  exact: real_integer_cell_borel hf.
have hub n : is_baire_function (u n) := (@integer_characteristic_term_baire R X c g hgb n).
apply: (@baire_function_pointwise_limit R X [the metricType R of real_line_metric R]
  (fun n x => \sum_(i < n) u i x) q).
- move=> n; exact: baire_real_finite_sum hub n.
- apply: pointwise_eventually_equal_limit=> x.
  have [j [hj hval]] := hq x.
  exists (pickle j).+1=> n hn; rewrite hval.
  apply: (@finite_single_supported_sum R (fun i => u i x) (pickle j) (c j) n).
  + exact: (@integer_characteristic_term_at R X A g c x j hg hj).
  + move=> i hi; apply: (@integer_characteristic_term_off R X A g c x j i hg _ hi).
    move=> l hl; exact: real_integer_cell_unique hl hj.
  + exact hn.
Qed.
