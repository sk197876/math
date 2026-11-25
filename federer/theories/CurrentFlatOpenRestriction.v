(** Federer (1969), 4.1.14, pp. 370–371: original
    flat currents restrict to the same compact index on a
    source neighbourhood. Actual test zero extension gives
    the flat norm nonincrease, and the same supported normal
    approximants prove flat membership. Original inclusion
    then recovers the original current. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentSupportGeometry
  CurrentOpenRestriction CurrentOpenRestrictionSupport CurrentOpenRestrictionNormal
  CurrentNeighbourhoodInclusion CurrentOpenIdentitySmooth CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentLipschitzCompactImage
  CurrentFlatFormSeminormLaws CurrentFlatDualSeminormUP CurrentFlatDualSeminormSealed
  CurrentFlatNorm CurrentFlatOpenTestExtension ExtendedSupremumUP
  NormalCurrentsUP FlatCurrentsUP FlatCurrentFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatOpenRestriction.
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
Variable K:smooth_compact_set hNX U.
Hypothesis hKZ:smooth_compact_carrier K `<=` Z.
Local Notation KZ := (@current_compact_index_in_open R n U Z K hKZ).
Local Notation CU := (@current_space R h2 n U hU m).
Local Notation CZ := (@current_space R h2 n Z hZ m).
Local Notation actionU := (@current_value R h2 n U hU m).
Local Notation actionZ := (@current_value R h2 n Z hZ m).
Local Notation restriction := (@current_open_restriction R h2 n m Z U hZ hU hZU).
Local Notation extension := (@current_open_test_extension R h2 n m Z U hZ hU hZU).
Local Notation FU := (@current_flat_norm R h2 n m U hU K).
Local Notation FZ := (@current_flat_norm R h2 n m Z hZ KZ).
Local Notation flatU := (@is_flat_current_supported_in R h2 n m U hU K).
Local Notation flatZ := (@is_flat_current_supported_in R h2 n m Z hZ KZ).

(** Source for [current_open_restriction_flat_norm_le]: the
    actual source restriction cannot increase the original
    fixed-K flat norm, supporting 4.1.14, pp. 370–371.
    The current is arbitrary and extended values are retained;
    no mass, support or representation premise is imposed. *)
Theorem current_open_restriction_flat_norm_le (T:CU):
  (FZ (restriction T)<=FU T)%E.
Proof.
apply:(extended_supremum_least (@CurrentFlatDualSeminorm.laws R h2 n m
  Z hZ KZ (actionZ (restriction T))))=>a [psi [hPsi hValue]].
apply:(extended_supremum_upper (@CurrentFlatDualSeminorm.laws R h2 n m
  U hU K (actionU T))).
exists (extension psi);split.
- rewrite (@current_open_test_flat_seminorm R h2 n m U Z hU hZ hZU K hKZ psi).
  exact:hPsi.
- rewrite -current_open_restriction_evaluation;exact:hValue.
Qed.

(** Source for [flat_current_open_restriction]: an original
    member of F_(m,K)(U) restricts to F_(m,K)(Z), supporting
    4.1.14, p. 370. The compact carrier remains exactly
    K. Restrict the same original supported normal approximants;
    normality of the candidate current is not required. *)
Theorem flat_current_open_restriction (T:CU):flatU T->flatZ (restriction T).
Proof.
move=>hFlat epsilon hEpsilon.
have[Q [[hNormal hSupport] hApprox]]:=hFlat epsilon hEpsilon.
exists (restriction Q);split.
- split.
  + apply:(@current_normal_neighbourhood_restriction R h2 n Z U hZ hU hZU m Q hNormal).
    move=>x hx;exact:hKZ x (hSupport x hx).
  + move=>x hx;apply:hSupport.
    exact:(@current_open_restriction_support_subset R h2 n m Z U hZ hU hZU Q x hx).
- rewrite -(linB (hom_linear restriction)).
  exact:le_lt_trans (current_open_restriction_flat_norm_le (T-Q)) hApprox.
Qed.

(** Source for [flat_current_neighbourhood_inclusion_recovery]:
    the original flat current is recovered by inclusion from
    its actual restriction, supporting the printed representative
    relation in 4.1.14, p. 370. Any compactness witness
    for the restricted current is allowed. The exact K and
    the original current and test spaces are retained. *)
Theorem flat_current_neighbourhood_inclusion_recovery
    (T:CU) (hT:flatU T)
    (hCompact:@compact (real_norm_metric_space hNX)
      (@current_support R h2 n Z hZ m (restriction T))):
  @current_compact_map_pushforward R h2 n n Z U hZ hU
    (fun x:X=>x) hZU (@current_open_identity_smooth R n Z hZ)
    m (restriction T) hCompact=T.
Proof.
have hSupport:@current_support R h2 n U hU m T `<=` Z.
  move=>x hx;apply:hKZ.
  exact:(@flat_current_supported_support R h2 n m U hU K T hT x hx).
pose hId:=@current_open_identity_smooth R n Z hZ.
pose hProper:=@current_compact_map_proper R h2 n n m Z U hZ (restriction T)
  (fun x:X=>x) hZU (norm_class_continuous (hId 0%N)) hCompact.
exact:(@current_neighbourhood_inclusion_recovery R h2 n m Z U hZ hU hZU
  hId T hSupport hProper).
Qed.
End CurrentFlatOpenRestriction.
