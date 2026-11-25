(** Federer (1969), 4.1.12, p. 367: the
    original compact flat-form seminorm is opaque.
    Its public interface exposes only the independent
    defining formula after proved existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet
  CurrentFlatFormSeminormUP CurrentFlatFormSeminormExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentFlatFormSeminormSignature.
(** Source for [value]: the original F_K on E^m(U),
    Federer 4.1.12, p. 367. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x),
  smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U->
  @current_smooth_space R h2 n U hU m->R.
(** Source for [laws]: precisely the original maximum
    formula, Federer 4.1.12, p. 367. No dual bound,
    continuity or decomposition conclusion is assumed. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U),
  @is_current_flat_form_seminorm R h2 n m U hU K (@value R h2 n m U hU K).
End CurrentFlatFormSeminormSignature.
Module CurrentFlatFormSeminorm:CurrentFlatFormSeminormSignature.
(** Source for [value]: seal the proved maximum
    witness, supporting Federer 4.1.12, p. 367. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U):
    @current_smooth_space R h2 n U hU m->R:=
  projT1 (cid (@current_flat_form_seminorm_exists R h2 n m U hU K)).
(** Source for [laws]: the sealed value has the
    independent original formula, supporting Federer
    4.1.12, p. 367. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U):
  @is_current_flat_form_seminorm R h2 n m U hU K (@value R h2 n m U hU K).
Proof. exact:(projT2 (cid (@current_flat_form_seminorm_exists R h2 n m U hU K))). Qed.
End CurrentFlatFormSeminorm.
