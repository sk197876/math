(** Federer (1969), 4.1.8, p. 361: when the
    first current has compact support, the second projection
    is proper on the actual product support. The proof
    uses the exact support identity and the original
    relative closedness and compact-rectangle laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms CurrentSpaces CurrentSupportGeometry SmoothCompactSet
  CurrentCartesianDomain CurrentCartesianCutoff CurrentCartesianProductSealed
  CurrentCartesianSupportUpper CurrentCartesianSupportLower CurrentProperSupport
  CurrentProperSupportRestriction FunctionalSupportRelativeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianProjectionProper.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation Image := (fun z (hz:AB z)=>hz.2).
Variable S:@current_space R h2 m A hA i.
Variable T:@current_space R h2 n B hB j.
Local Notation supportS := (@current_support R h2 m A hA i S).
Local Notation supportT := (@current_support R h2 n B hB j T).
Local Notation Product := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T).

(** Source for [current_cartesian_projection_proper_on_support]:
    compactness of spt S suffices for the original
    second-projection pushforward q#(S times T), supporting
    Federer 4.1.8, p. 361. The exact original
    support is used, with no compactness premise on T. *)
Theorem current_cartesian_projection_proper_on_support:
  @compact (real_norm_metric_space hNX) [set x|supportS x]->
  @is_current_proper_on_support R h2 (m+n) n (i+j) AB hAB B Product q Image.
Proof.
move=>hCompact.
apply:(@current_proper_support_compact_loci R h2 (m+n) n AB hAB B q Image (i+j) Product).2=>K.
pose KA:=@Build_smooth_compact_set R X NX hNX A supportS (fun x hx=>hx.1) hCompact.
have[C [hClosed hSupport]]:=@functional_support_relative_closed R Y (A_m Y R^o j) NY hNY B
  (@current_test_space R h2 n B hB j) (@current_test_value R h2 n B hB j)
  (@current_value R h2 n B hB j T).
have hTSupport:supportT=B `&` C:=hSupport.
pose KB:=@Build_smooth_compact_set R Y NY hNY B (smooth_compact_carrier K `&` C)
  (fun y hy=>smooth_compact_in_domain K y hy.1)
  (compact_closedI (smooth_compact_is_compact K) hClosed).
have[KC hKC]:=@current_cartesian_compact_rectangle R m n A B KA KB.
have hEqual:[set z|@current_support R h2 (m+n) AB hAB (i+j) Product z /\
    smooth_compact_carrier K (q z)]=smooth_compact_carrier KC.
  apply:funext=>z;apply:propext;split.
  - move=>[hProduct hK].
    have hFactors:=@current_cartesian_support_upper R h2 m n i j A B hA hB S T z hProduct.
    have hTC:(B `&` C) (q z) by rewrite -hTSupport;exact:hFactors.2.
    rewrite hKC;split;first exact:hFactors.1.
    exact:conj hK hTC.2.
  - move=>hPoint.
    rewrite hKC in hPoint.
    have hS:supportS (p z):=hPoint.1.
    have hK:smooth_compact_carrier K (q z):=hPoint.2.1.
    have hTC:C (q z):=hPoint.2.2.
    have hT:supportT (q z).
      rewrite hTSupport;exact:conj (smooth_compact_in_domain K (q z) hK) hTC.
    split;last exact:hK.
    exact:(@current_cartesian_support_lower R h2 m n i j A B hA hB S T z (conj hS hT)).
rewrite hEqual;exact:smooth_compact_is_compact KC.
Qed.
End CurrentCartesianProjectionProper.
