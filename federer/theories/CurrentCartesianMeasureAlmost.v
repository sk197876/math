(** Federer (1969), 4.1.11, p. 365: transport factor
    conull assertions to the original Euclidean product
    measure. These adapters use only the already proved
    2.6.1 rectangle laws and 4.1.8 coordinate bijection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentDomain
  CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws CurrentCartesianMeasureSealed
  CurrentCartesianMeasureRadon CartesianMeasureAlmost MeasureUP MeasureAlmostUP
  MeasureAlmostBasic ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section CurrentCartesianMeasureAlmost.
Variable R:realType.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n)%N (@euclidean_cartesian_set R m n A B)).
Local Notation PT := (Choice.clone (AT*BT)%type _).
Variables (alpha:set AT->\bar R) (beta:set BT->\bar R).
Hypothesis hAlpha:is_measure alpha.
Hypothesis hBeta:is_measure beta.
Local Notation lambda := (@CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta).
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).
Local Notation J := (@CartesianCurrentDomain.join R m n A B).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).
Local Notation hBij := (@current_cartesian_measure_bijection R m n A B alpha beta hAlpha hBeta).

(** Source for [current_cartesian_measure_first_almost]:
    a conull first-factor assertion holds on the actual
    original product domain, supporting the sharp join
    integral in Federer 4.1.11, p. 365. No total-mass
    finiteness or Radon assumption is needed for this adapter. *)
Theorem current_cartesian_measure_first_almost (P:set AT):
  measure_almost_everywhere alpha P->
  measure_almost_everywhere lambda [set z:CT|P (D z).1].
Proof.
move=>hP.
have hFirst:=@product_almost_everywhere_first_factor R AT BT alpha beta hAlpha hBeta P hP.
apply:(@measure_bijection_almost_everywhere_iff R PT CT mu lambda J D hBij _).1.
apply:(@measure_almost_everywhere_mono R PT mu hm _ _ _ hFirst)=>z hz.
by change (P (D (J z)).1);rewrite current_cartesian_domain_join_split.
Qed.

(** Source for [current_cartesian_measure_second_almost]:
    the corresponding second-factor assertion holds on
    the actual original product domain, supporting Federer
    4.1.11, p. 365, with zero and infinite factor masses. *)
Theorem current_cartesian_measure_second_almost (P:set BT):
  measure_almost_everywhere beta P->
  measure_almost_everywhere lambda [set z:CT|P (D z).2].
Proof.
move=>hP.
have hSecond:=@product_almost_everywhere_second_factor R AT BT alpha beta hAlpha hBeta P hP.
apply:(@measure_bijection_almost_everywhere_iff R PT CT mu lambda J D hBij _).1.
apply:(@measure_almost_everywhere_mono R PT mu hm _ _ _ hSecond)=>z hz.
by change (P (D (J z)).2);rewrite current_cartesian_domain_join_split.
Qed.
End CurrentCartesianMeasureAlmost.
