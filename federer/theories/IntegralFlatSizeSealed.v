(** Federer (1969), 4.1.24, p. 382: seal the
    original integral flat infimum after proving existence.
    Only the real value and its independent original
    decomposition laws are exposed. No minimising witness,
    real homogeneity or construction is public. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces IntegralCurrentClassesUP
  IntegralFlatSizeUP IntegralFlatSizeExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type IntegralFlatSizeSignature.
(** Source for [value]: the finite infimum of the
    original same-K rectifiable costs, Federer 4.1.24, p. 382. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m),
  @is_integral_flat_current_supported_in R h2 n U hU m K T->R.
(** Source for [laws]: the opaque value satisfies the
    original lower-bound and approximation laws, p. 382. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integral_flat_current_supported_in R h2 n U hU m K T),
  @is_integral_flat_size R h2 n m U hU K T (@value R h2 n m U hU K T hT).
End IntegralFlatSizeSignature.

Module IntegralFlatSize:IntegralFlatSizeSignature.
(** Source for [value]: select only the independently
    proved infimum value, Federer 4.1.24, p. 382. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integral_flat_current_supported_in R h2 n U hU m K T):R:=
  projT1 (cid (@integral_flat_size_exists R h2 n m U hU K T hT)).
(** Source for [laws]: the hidden existence witness
    proves exactly the original specification, p. 382. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integral_flat_current_supported_in R h2 n U hU m K T):
  @is_integral_flat_size R h2 n m U hU K T (@value R h2 n m U hU K T hT).
Proof. exact:projT2 (cid (@integral_flat_size_exists R h2 n m U hU K T hT)). Qed.
End IntegralFlatSize.

Arguments IntegralFlatSize.value : clear implicits.
Arguments IntegralFlatSize.laws : clear implicits.
