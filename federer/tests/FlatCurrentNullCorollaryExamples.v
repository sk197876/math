(** Actual-space checks of Federer (1969), 4.1.21,
    p. 378. Exercise both final original corollaries,
    including the empty set, the whole-domain choice of
    B, and the zero-dimensional ambient endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentSupportGeometry CurrentSupportExtensionality
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentMassSealed
  CurrentFiniteMassRepresentation FlatCurrentsUP IntegralGeometricMeasure
  MeasureUP MeasureBasic FlatCurrentNullCorollaries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCurrentNullCorollaryExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Variable U:set (R_n R n).
Local Notation X:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable T:@current_space R h2 n U hU m.
Local Notation support:=(@current_support R h2 n U hU m T).
Local Notation IG:=(@integral_geometric_measure R n m hMN 1%E).

(** Source for [relative_null_support_whole_domain]: setting
    B=U in the actual first corollary recovers the
    preceding null-support conclusion, Federer 4.1.20–4.1.21,
    p. 378. This checks that neither a mass premise
    nor a representation premise has entered the theorem. *)
Example relative_null_support_whole_domain:
  (0<m)%N->@is_flat_current R h2 n m U hU T->
  IG support=0%E->T=0.
Proof.
move=>hPositive hFlat hNull.
have hDifference:support `\` U=set0.
  apply/seteqP;split;last by move=>x [].
  by move=>x [hx hn];exact:False_ind _ (hn hx.1).
have hRelative:@closed (subspace (U:set XT)) (support `\` U).
  rewrite hDifference;exact:closed0.
have hIntersect:U `&` support=support.
  apply/seteqP;split;first by move=>x [_ hx].
  by move=>x hx;split;first exact:hx.1.
have hNullIntersect:IG (U `&` support)=0%E by rewrite hIntersect.
have hSupport:=@current_flat_relative_integral_geometric_null
  R h2 n m hMN U hU T U hPositive hFlat (fun x hx=>hx) hRelative hNullIntersect.
apply:(@current_empty_support_iff_zero R h2 n m U hU T).1=>x hx.
have hBad:=hSupport x hx;exact:False_ind _ (hBad.2 hBad.1).
Qed.

(** Source for [flat_null_variation_empty_set]: the actual
    second corollary includes the empty arbitrary subset,
    Federer 4.1.21, p. 378. Its original representation
    is derived internally from finite mass. *)
Example flat_null_variation_empty_set
    (hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E):
  (0<m)%N->@is_flat_current R h2 n m U hU T->
  let hT:=@current_finite_mass_representation R h2 n m U hU T hFinite in
  @NormalisedCurrent.measure R h2 n m U hU T hT
    [set x:current_domain R n U|(@set0 X) (set_val x)]=0%E.
Proof.
move=>hPositive hFlat.
apply:(@current_flat_integral_geometric_null_variation
  R h2 n m hMN U hU T hFinite set0 hPositive hFlat).
- by move=>x [].
- exact:(measure_empty
    (@integral_geometric_measure_is_measure R n m hMN 1%E (lexx _))).
Qed.
End FlatCurrentNullCorollaryExamples.

(** Source for [positive_current_on_zero_space_has_empty_support]:
    the actual ambient R^0 endpoint of the positive-degree
    corollaries, Federer 4.1.21, p. 378, through the
    original current-space vanishing theorem of 4.1.10,
    p. 364. No point or nonempty-domain premise is supplied. *)
Example positive_current_on_zero_space_has_empty_support
    (R:realType) (h2:(1+1:R)!=0) (U:set (R_n R 0%N))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R 0%N)) U x)
    (T:@current_space R h2 0%N U hU 1%N):
  @current_support R h2 0%N U hU 1%N T `<=` set0.
Proof.
exact:(@current_null_corollary_above_dimension_support
  R h2 0%N 1%N (ltn0Sn 0%N) U hU T).
Qed.
