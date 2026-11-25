(** Federer (1969), 4.1.14, p. 370: an original flat
    representative S on a source neighbourhood Z, whose literal
    inclusion image is T, is exactly the original open restriction
    of T. This identity is independent of normality. When the
    original T is normal with support in K, the preceding normal
    restriction theorem then proves normality of S without a
    circular premise on the representative. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentSupportGeometry
  CurrentOpenRestriction CurrentCompactInclusionRestriction
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra CurrentOpenIdentitySmooth
  CurrentOpenRestrictionNormal CurrentLipschitzCompactImage
  NormalCurrentsUP FlatCurrentsUP FlatCurrentFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatNeighbourhoodRepresentative.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables U Z:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hZ:forall x,Z x->norm_domain_interior NX Z x.
Hypothesis hZU:forall x,Z x->U x.
Local Notation CU := (@current_space R h2 n U hU m).
Local Notation CZ := (@current_space R h2 n Z hZ m).
Local Notation hId := (@current_open_identity_smooth R n Z hZ).
Local Notation restriction := (@current_open_restriction R h2 n m Z U hZ hU hZU).
Local Notation inclusion S hS := (@current_compact_map_pushforward R h2 n n
  Z U hZ hU (fun x:X=>x) hZU hId m S hS).

(** Source for [current_compact_representative_is_open_restriction]:
    the representative in the defining convergence condition of
    Federer 4.1.14, p. 370, is the original restriction.
    The preceding inclusion-restriction law of 4.1.10, p. 364,
    proves this for every compact actual current, independently
    of flatness, normality or representation by integration. *)
Theorem current_compact_representative_is_open_restriction
    (T:CU) (S:CZ)
    (hCompact:@compact (real_norm_metric_space hNX)
      (@current_support R h2 n Z hZ m S)):
  inclusion S hCompact=T->S=restriction T.
Proof.
move=>hImage.
pose hProper:=@current_compact_map_proper R h2 n n m Z U hZ S
  (fun x:X=>x) hZU (norm_class_continuous (hId 0%N)) hCompact.
have hRecovery:=@current_compact_inclusion_restriction R h2 n Z U hZ hU hZU
  m S hCompact hId hProper.
change (restriction (inclusion S hCompact)=S) in hRecovery.
rewrite hImage in hRecovery;exact:esym hRecovery.
Qed.

Variable K:smooth_compact_set hNX U.
Hypothesis hKZ:smooth_compact_carrier K `<=` Z.
Local Notation KZ := (@current_compact_index_in_open R n U Z K hKZ).
Local Notation flatZ := (@is_flat_current_supported_in R h2 n m Z hZ KZ).
Local Notation compactFlat S hS := (@flat_supported_current_compact R h2 n m
  Z hZ KZ S hS).

(** Source for [current_flat_representative_is_open_restriction]:
    every original flat representative under the inclusion in
    Federer 4.1.14, p. 370, is the open restriction of T.
    It uses the exact unchanged K package and the same compactness
    witness as the original independent approximation specification.
    No normality or integration premise on S is added. *)
Theorem current_flat_representative_is_open_restriction
    (T:CU) (S:CZ) (hS:flatZ S):
  inclusion S (compactFlat S hS)=T->S=restriction T.
Proof.
exact:(@current_compact_representative_is_open_restriction T S (compactFlat S hS)).
Qed.

(** Source for [current_normal_flat_representative]: if the
    original T is normal in K, then every printed flat
    representative S under inclusion is normal in the same K
    on Z, supporting the first construction step of Federer
    4.1.14, p. 370. Normality follows after identifying S
    with the restriction; it is not assumed of S. *)
Theorem current_normal_flat_representative
    (T:CU) (hT:@normal_currents_supported_in R h2 n U hU m K T)
    (S:CZ) (hS:flatZ S):
  inclusion S (compactFlat S hS)=T->
  @normal_currents_supported_in R h2 n Z hZ m KZ S.
Proof.
move=>hImage.
have hIdentity:=@current_flat_representative_is_open_restriction T S hS hImage.
split.
- rewrite hIdentity.
  apply:(@current_normal_neighbourhood_restriction R h2 n Z U hZ hU hZU m T hT.1).
  move=>x hx;exact:hKZ x (hT.2 x hx).
- exact:(@flat_current_supported_support R h2 n m Z hZ KZ S hS).
Qed.
End CurrentFlatNeighbourhoodRepresentative.
