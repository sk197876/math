(** Federer (1969), 4.1.12, p. 367: the
    opaque original dual flat seminorm. Its public
    laws give exactly the independent supremum over
    actual compact tests; continuity is proved later. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  Hom GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentFlatDualSeminormUP CurrentFlatDualSeminormExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentFlatDualSeminormSignature.
(** Source for [value]: the original F_K(T),
    Federer 4.1.12, p. 367. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x),
  smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U->
  Hom (@current_test_space R h2 n U hU m) R^o->\bar R.
(** Source for [laws]: exactly the original
    unit flat-seminorm test supremum, Federer 4.1.12, p. 367. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
  (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
  (T:Hom (@current_test_space R h2 n U hU m) R^o),
  @is_current_flat_dual_seminorm R h2 n m U hU K T (@value R h2 n m U hU K T).
End CurrentFlatDualSeminormSignature.
Module CurrentFlatDualSeminorm:CurrentFlatDualSeminormSignature.
(** Source for [value]: hide the proved
    flat-supremum witness, supporting Federer
    4.1.12, p. 367. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:Hom (@current_test_space R h2 n U hU m) R^o): \bar R:=
  projT1 (cid (@current_flat_dual_seminorm_exists R h2 n m U hU K T)).
(** Source for [laws]: the hidden value
    satisfies the independent original flat-seminorm law,
    supporting Federer 4.1.12, p. 367. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:Hom (@current_test_space R h2 n U hU m) R^o):
  @is_current_flat_dual_seminorm R h2 n m U hU K T (@value R h2 n m U hU K T).
Proof. exact:(projT2 (cid (@current_flat_dual_seminorm_exists R h2 n m U hU K T))). Qed.
End CurrentFlatDualSeminorm.
