(** Federer (1969), 3.4.5, p. 321: coordinate
    equations in the cited local analytic example are analytic
    by the bounded-linear assertion of 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormOpenDomainLaws NormAnalyticUP NormAnalyticLinear EuclideanScalarCoordinateMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_scalar_coordinate_analytic]: the
    actual coordinate functions in finite analytic equations,
    supporting the example cited at 3.4.5, p. 321.
    All finite dimensions and original coordinates are retained. *)
Lemma euclidean_scalar_coordinate_analytic (R:realType) n (i:'I_n):
  @norm_analytic R (R_n R n) R^o (inner_norm (@euclidean_inner_productP R n)) (fun z=>`|z|)
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (@scalar_absolute_value_norm R)
    setT (fun v=>v i).
Proof.
exact:(@norm_bounded_linear_analytic R (R_n R n) R^o
  (inner_norm (@euclidean_inner_productP R n)) (fun z=>`|z|)
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (@scalar_absolute_value_norm R)
  setT (fun v _=>norm_full_domain_interior _ v) (euclidean_scalar_coordinate_map i)
  (euclidean_scalar_coordinate_bounded i)).
Qed.
