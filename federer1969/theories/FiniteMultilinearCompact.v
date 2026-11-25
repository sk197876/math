(** Federer (1969), 3.4.5, p. 319, using
    1.10.5: bounded scalar derivative coefficients range in
    compact sets when the original source is finite dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LinearBasis ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm FiniteNormMetricCompactness FiniteMultilinearCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_scalar_derivative_ball_compact]: the
    finite-dimensional coefficient compactness used in 3.4.5,
    p. 319. A basis of the original source supplies a
    proved finite basis of each actual derivative space; the
    previously proved norm-ball compactness theorem then applies.
    Order zero, zero source dimension and empty balls remain. *)
Theorem finite_scalar_derivative_ball_compact (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b) m (r:R):
  @compact (real_norm_metric_space (continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
    (@ContinuousMultilinear.laws R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))))
    [set z|@ContinuousMultilinear.norm R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) z<=r].
Proof.
have [q [e [he hDimension]]]:=@finite_scalar_multilinear_basis_exists R X NX hNX n b hb m.
exact:(@finite_norm_metric_ball_compact R
  (@ContinuousMultilinear.space R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
  (@ContinuousMultilinear.norm R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
  (continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
    (@ContinuousMultilinear.laws R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)))
  q e he r).
Qed.
