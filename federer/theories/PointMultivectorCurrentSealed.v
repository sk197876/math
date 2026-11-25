(** Federer (1969), 4.1.9, p. 363: the original point
    multivector current is opaque. Its linear multivector map
    and literal test action are the only public data. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentSpaces
  PointMultivectorCurrentUP PointMultivectorCurrentExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type PointMultivectorCurrentSignature.
(** Source for [value]: the current T(beta)=<eta,beta(x)>,
    linear in eta, Federer 4.1.9, p. 363. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n j:nat)
    (U:set (R_n R n))
    (hU:forall y,U y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U y)
    (x:R_n R n) (hx:U x),
  Hom (exterior_power (R_n R n) j) (@current_space R h2 n U hU j).
(** Source for [laws]: the original point pairing on every
    actual compact test, supporting Federer 4.1.9, p. 363. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n j:nat)
    (U:set (R_n R n))
    (hU:forall y,U y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U y)
    (x:R_n R n) (hx:U x),
  @is_point_multivector_current R h2 n j U hU x (@value R h2 n j U hU x hx).
End PointMultivectorCurrentSignature.
Module PointMultivectorCurrent:PointMultivectorCurrentSignature.
(** Source for [value]: seal the proved original point
    current witness, supporting Federer 4.1.9, p. 363. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n j:nat)
    (U:set (R_n R n))
    (hU:forall y,U y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U y)
    (x:R_n R n) (hx:U x):
  Hom (exterior_power (R_n R n) j) (@current_space R h2 n U hU j):=
  projT1 (cid (@point_multivector_current_exists R h2 n j U hU x hx)).
(** Source for [laws]: the opaque witness satisfies its
    independently specified original action, supporting
    Federer 4.1.9, p. 363. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n j:nat)
    (U:set (R_n R n))
    (hU:forall y,U y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U y)
    (x:R_n R n) (hx:U x):
  @is_point_multivector_current R h2 n j U hU x (@value R h2 n j U hU x hx).
Proof. exact:(projT2 (cid (@point_multivector_current_exists R h2 n j U hU x hx))). Qed.
End PointMultivectorCurrent.
