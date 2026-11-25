(** Actual-space boundary checks for Federer (1969),
    4.1.12, pp. 367–368: the
    nonzero point current in R^0 is
    flat with its singleton index and
    has flat norm one. With the
    empty index its flat value is infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentSpaces CurrentDirac
  CurrentSupportGeometry DiracCurrentBounds CurrentMassSealed CurrentMassBasic CurrentGlobalComassSealed CurrentGlobalComassBound
  CurrentZeroCovectorMaps CurrentBoundedPointTest CurrentAboveDimension SmoothCompactSet
  NormalCurrentsUP CurrentFlatNorm CurrentFlatFiniteSupport FlatCurrentsUP FlatCurrentFinite FlatCurrentMassNoFillings.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentEndpointExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation P := (@dirac_current R h2 0%N Full hFull (0:X)).
Local Notation M := (@CurrentMass.value R h2 0%N 0%N Full hFull).

(** Source for [flat_point_singleton_index]: the
    actual singleton compact in the
    dimension-zero case of the original
    compact-index definitions, Federer 4.1.12,
    pp. 367–368. *)
Definition flat_point_singleton_index:smooth_compact_set hNX Full:=
  @Build_smooth_compact_set R X NX hNX Full [set (0:X)]
    (fun _ _=>Logic.I) (@compact_set1 (real_norm_metric_space hNX) (0:X)).
Local Notation K := flat_point_singleton_index.

(** Source for [zero_dimensional_point_mass_one]:
    the actual original point current
    has mass one even in R^0,
    checking the zero-degree endpoint used
    by Federer 4.1.12, pp. 367–368. *)
Example zero_dimensional_point_mass_one:M P= 1%:E.
Proof.
have[gamma [hSupport [hRange hOne]]]:=@current_bounded_point_test_exists R h2 0%N (0:X) 1 ltr01.
have hUnit:(@CurrentGlobalComass.value R h2 0%N 0%N Full
    (@current_test_value R h2 0%N Full hFull 0%N gamma)<=1)%E.
  apply:(@current_global_comass_bound R h2 0%N 0%N Full
    (@current_test_value R h2 0%N Full hFull 0%N gamma) 1).2=>x _.
  rewrite current_zero_form_coefficient_norm (ger0_norm (andP (hRange x)).1).
  exact:(andP (hRange x)).2.
have hLower:=@current_mass_unit_test_upper R h2 0%N 0%N Full hFull P gamma hUnit.
rewrite dirac_current_evaluation hOne zero_formK in hLower.
have hUpper:=(@dirac_current_finite_mass R h2 0%N Full hFull (0:X) Logic.I).1.
apply/eqP;by rewrite eq_le hUpper hLower.
Qed.

(** Source for [zero_dimensional_point_flat]: the
    nonzero original point current belongs
    to its actual singleton flat space,
    checking the retained R^0 case of
    Federer 4.1.12, p. 368. *)
Example zero_dimensional_point_flat:
  @is_flat_current_supported_in R h2 0%N 0%N Full hFull K P.
Proof.
apply:supported_normal_current_is_flat;split.
- exact:(@dirac_current_normal R h2 0%N Full hFull (0:X) Logic.I).
- exact:(@dirac_current_support_subset R h2 0%N Full hFull (0:X) Logic.I).
Qed.

(** Source for [zero_dimensional_point_flat_norm_one]:
    the actual singleton flat norm
    of the original R^0 point
    equals one, checking the degree-zero
    norm and no-filling endpoints of
    Federer 4.1.12, pp. 367–368. *)
Example zero_dimensional_point_flat_norm_one:
  @current_flat_norm R h2 0%N 0%N Full hFull K P= 1%:E.
Proof.
have hNoFilling (S:@current_space R h2 0%N Full hFull 1%N):
    @is_normal_current R h2 0%N Full hFull 1%N S->
    @current_support R h2 0%N Full hFull 1%N S `<=` smooth_compact_carrier K->S=0.
  move=>_ _;exact:(@current_above_dimension R h2 0%N 1%N (ltn0Sn 0%N) Full hFull S).
have h:=(@flat_current_mass_equals_flat_no_fillings R h2 0%N 0%N Full hFull K
  hNoFilling P zero_dimensional_point_flat).1.
by rewrite h zero_dimensional_point_mass_one.
Qed.

(** Source for [empty_index_point_flat_value_infinite]:
    the same actual nonzero point
    has infinite F_empty, checking that
    the original arbitrary compact-index supremum
    is not silently made finite,
    Federer 4.1.12, p. 367. *)
Example empty_index_point_flat_value_infinite:
  @current_flat_norm R h2 0%N 0%N Full hFull
    (@smooth_compact_empty R X NX hNX Full) P=(+oo)%E.
Proof.
pose E:=@smooth_compact_empty R X NX hNX Full.
pose F:=@current_flat_norm R h2 0%N 0%N Full hFull E P.
have hNotFinite:~(F< +oo)%E.
  move=>hFinite.
  have hSupport:=@current_finite_flat_functional_support R h2 0%N 0%N Full hFull E
    (@current_value R h2 0%N Full hFull 0%N P) hFinite.
  have hPoint:@current_support R h2 0%N Full hFull 0%N P (0:X).
    rewrite (@dirac_current_support R h2 0%N Full hFull (0:X) Logic.I);exact:erefl.
  exact:(hSupport (0:X) hPoint).
have hTop:((+oo)%E<=F)%E by rewrite leNgt;apply/negP;exact:hNotFinite.
apply/eqP;by rewrite eq_le leey hTop.
Qed.
End FlatCurrentEndpointExamples.
