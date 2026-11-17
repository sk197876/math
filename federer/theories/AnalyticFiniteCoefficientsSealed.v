(** Supporting Federer (1969), 3.4.8(5), p. 328:
    exact finite Taylor coefficients behind the original value law.
    The existence implementation stays opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRing FiniteJetDegreeIndices
  AnalyticFiniteCoefficientsUP AnalyticFiniteCoefficientsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type AnalyticFiniteCoefficientsSignature.
(** Source for [map]: original finite Taylor coefficients,
    supporting Federer 3.4.8(5), p. 328. *)
Parameter map:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) l a,@analytic_germ_ring R X NX hNX a->
    {ffun finite_jet_degree_indices n l->R^o}.
(** Source for [laws]: independent exact derivative and factorial
    values, supporting Federer 3.4.8(5), p. 328. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) l a,is_analytic_finite_coefficient_map e (@map R X NX hNX n e l a).
End AnalyticFiniteCoefficientsSignature.
Module AnalyticFiniteCoefficients:AnalyticFiniteCoefficientsSignature.
(** Source for [map]: private choice from proved exact coefficient
    existence, supporting Federer 3.4.8(5), p. 328. *)
Definition map (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (e:'I_n->X) l a:=
  projT1 (cid (@analytic_finite_coefficient_map_exists R X NX hNX n e l a)).
(** Source for [laws]: the chosen map satisfies the independent
    original value law, supporting Federer 3.4.8(5), p. 328. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (e:'I_n->X) l a:
  is_analytic_finite_coefficient_map e (@map R X NX hNX n e l a).
Proof. exact:(projT2 (cid (@analytic_finite_coefficient_map_exists R X NX hNX n e l a))). Qed.
End AnalyticFiniteCoefficients.
