(** Federer (1969), 4.1.18, p. 375: existence of
    the original pair map into F_m(U). Corestrict the
    already independently specified current-valued q using
    the existing opaque linear-subspace lift. Do not replace
    the original flat-union carrier by a newly chosen quotient. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces FlatCurrentClosure FlatCurrentUnion CurrentLonePairImageUP
  CurrentLonePairImageSealed CurrentLonePairGlobalFlat
  FlatCurrentUnionSpace CurrentLonePairFlatUP LinearSubspaceLiftSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_lone_pair_flat_map_exists]: the
    exact defining inclusion equation has an actual linear
    witness, Federer 4.1.18, p. 375. Surjectivity and the
    kernel formula are separate conclusions. *)
Theorem current_lone_pair_flat_map_exists (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x):
  exists Q:Hom (@current_lone_pair_space R h2 n m U hU)
      (@flat_current_union_space R h2 n m U hU),
    @is_current_lone_pair_flat_map R h2 n m U hU Q.
Proof.
pose S:=@flat_current_union_subspace R h2 n m U hU.
pose inc:=@flat_current_union_inclusion R h2 n m U hU.
pose laws:=@flat_current_union_space_laws R h2 n m U hU.
pose q:=@CurrentLonePair.map R h2 n m U hU.
pose hRange:=@current_lone_pair_is_flat R h2 n m U hU.
exists (@LinearSubspaceLift.map R _ _ _ S inc laws q hRange).
move=>v;exact:(@LinearSubspaceLift.evaluation R _ _ _ S inc laws q hRange v).
Qed.
