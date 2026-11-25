(** Federer (1969), 4.1.18, p. 375: opaque
    original L1 pair map q. Only its actual linear
    map and independent defining equation are public;
    the existence witness is hidden by the signature. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentLonePairImageUP CurrentLonePairImageExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentLonePairSignature.
(** Source for [map]: the original linear q of
    Federer 4.1.18, p. 375. Its compact flat
    range and onto assertion are proved separately. *)
Parameter map:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat)
  (U:set (R_n R n))
  (hU:forall x,U x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) U x),
  Hom (@current_lone_pair_space R h2 n m U hU)
    (@current_space R h2 n U hU m).
(** Source for [laws]: every actual pair has the
    original density-plus-boundary value, Federer 4.1.18,
    p. 375, on the unchanged original open U. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat)
  (U:set (R_n R n))
  (hU:forall x,U x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) U x),
  @is_current_lone_pair_map R h2 n m U hU (@map R h2 n m U hU).
End CurrentLonePairSignature.
Module CurrentLonePair:CurrentLonePairSignature.
(** Source for [map]: select the already proved
    witness of q, supporting Federer 4.1.18, p. 375. *)
Definition map (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x):
    Hom (@current_lone_pair_space R h2 n m U hU)
      (@current_space R h2 n U hU m):=
  projT1 (cid (@current_lone_pair_map_exists R h2 n m U hU)).
(** Source for [laws]: the opaque witness satisfies
    the independent original q equation, supporting
    Federer 4.1.18, p. 375. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x):
  @is_current_lone_pair_map R h2 n m U hU (@map R h2 n m U hU).
Proof. exact:(projT2 (cid (@current_lone_pair_map_exists R h2 n m U hU))). Qed.
End CurrentLonePair.
