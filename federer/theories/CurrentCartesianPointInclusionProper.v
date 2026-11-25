(** Federer (1969), 4.1.8, p. 362: epsilon_z
    is proper on every original current support. Reuse
    its actual affine smoothness and q epsilon_z=id,
    together with the original compact support criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormClassZeroTopology
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentDomain CurrentSpaces CurrentProperSupport
  CurrentCartesianDomain CurrentCartesianPointInclusion CurrentCartesianProjections CurrentSplitMapProperSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianPointInclusionProper.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation hFull := (fun (y:Y) (_:True)=>@norm_full_domain_interior R Y NY y).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Variable z:X.
Hypothesis hz:A z.
Variable T:@current_space R h2 n B hB j.
Local Notation f := (@current_cartesian_point_inclusion R m n z).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation Image := (fun y hy=>@current_cartesian_point_inclusion_image R m n A B z hz y hy).

(** Source for [current_cartesian_point_inclusion_proper]:
    the original epsilon_z is proper on spt T,
    supporting delta_z times T=epsilon_z#T in
    Federer 4.1.8, p. 362. No compactness of
    spt T or whole-source properness assumption is added. *)
Theorem current_cartesian_point_inclusion_proper:
  @is_current_proper_on_support R h2 n (m+n) j B hB AB T f Image.
Proof.
have hAll:=@current_cartesian_point_inclusion_smooth R m n (fun _=>True) hFull z.
have hFZero:=(@norm_class_zeroP R Y Z NY NZ hNY hNZ (fun _=>True) f).1 (hAll 0%N).
have hFC:continuous (f:real_norm_metric_space hNY->real_norm_metric_space hNZ).
  move=>y;exact:(@norm_class_zero_continuous_at R Y Z NY NZ hNY hNZ
    (fun _=>True) f y hFZero Logic.I).
have hQAll:=@current_cartesian_last_projection_smooth R m n A B hA hB.
have hQZero:=(@norm_class_zeroP R Z Y NZ NY hNZ hNY AB q).1 (hQAll 0%N).
apply:(@current_split_map_proper_on_support R h2 n (m+n) j B AB hB T f q Image
  (fun y hy=>hy.2) _ hFC hQZero).
move=>y _;exact:current_cartesian_point_inclusion_left_inverse.
Qed.
End CurrentCartesianPointInclusionProper.
