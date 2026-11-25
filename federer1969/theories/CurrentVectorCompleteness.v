(** Federer (1969), 4.1.18, pp. 375–376: the
    actual finite-dimensional multivector coefficient spaces
    meet the earlier complete and separable normed-space
    hypotheses used for L1 fields. Reuse the
    original exterior basis and norm-equivalence results. *)
From mathcomp Require Import all_boot all_order all_algebra
  reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP
  VectorDaniellHypotheses GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentCoefficientNorms CurrentVectorSpaces
  FiniteNormMetricPolish.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section VectorCompleteness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation V:=(exterior_power (R_n R n) m).
Local Notation N:=(@current_vector_mass R h2 n m).
Local Notation hN:=(@current_vector_mass_real_norm R h2 n m).

(** Source for [current_multivector_mass_complete]:
    completeness of the actual mass-normed coefficient
    space used in the L1 series of Federer
    4.1.18, p. 376, by the finite basis
    of 1.3.4, p. 17. All degrees are retained. *)
Theorem current_multivector_mass_complete:
  is_complete_metric_space (real_norm_metric_space hN).
Proof.
have[k [b hb]]:=@current_vector_finite_basis R h2 n m.
exact:(@finite_norm_metric_complete R V N hN k b hb).
Qed.

(** Source for [current_multivector_mass_separable]:
    the actual multivector coefficient space is
    separable, discharging the L1 membership premise
    for compact smooth fields in Federer 4.1.18,
    pp. 375–376. No infinite-dimensional target hypothesis
    is added to a current assertion. *)
Theorem current_multivector_mass_separable:is_separable_normed_space hN.
Proof.
have[k [b hb]]:=@current_vector_finite_basis R h2 n m.
exact:(@finite_norm_metric_separable R V N hN k b hb).
Qed.
End VectorCompleteness.
