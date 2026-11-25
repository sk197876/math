(** Federer (1969), 4.1.12, p. 369: all
    positively oriented scalar intervals share one
    unit-comass test equal to DX on
    their common compact interval. This supplies
    the lower bound for the exact printed
    mass of their positive weighted sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneNormDifferential
  EuclideanScalarCoordinateMaps EuclideanCoordinateForms OneFormIdentification AlternatingForms AlternatingZero
  AlternatingFormUnitBounds CurrentFormInducedNorm CurrentCoefficientNorms CurrentZeroCovectorMaps
  CurrentSpaces CurrentConstantFields CurrentScalarCutoffFormTest CurrentBoundedNeighbourhoodTest
  ScalarCurrentIntervalCompact SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarCurrentCalibrationTest.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation DT := (@current_test_space R h2 1%N Full hFull 1%N).
Local Notation value := (@current_test_value R h2 1%N Full hFull 1%N).
Local Notation N1 := (@current_form_comass R h2 1%N 1%N).
Local Notation dx := (@euclidean_coordinate_form R 1%N ord0).

(** Source for [scalar_current_coordinate_comass_le_one]:
    the original unit coordinate covector DX
    has comass at most one, supporting
    the exact mass calculation in Federer
    4.1.12, p. 369. Reuse
    the original induced unit-tuple norm. *)
Lemma scalar_current_coordinate_comass_le_one:N1 dx<=1.
Proof.
apply:(alternating_form_unit_tuple_least hNX (@scalar_absolute_value_norm R)
  (@current_form_comass_is_induced R h2 1%N 1%N dx) (@ler01 R))=>t hUnit.
case/tupleP:t hUnit=>v rest hUnit.
rewrite (tuple0 rest) in hUnit *.
rewrite /euclidean_coordinate_form one_formE /euclidean_scalar_coordinate_map /=.
rewrite -euclidean_one_norm_coordinate.
exact:hUnit ord0.
Qed.

(** Source for [scalar_current_calibration_test_exists]:
    one actual compact test has comass
    at most one everywhere and equals
    the original DX throughout [a,b].
    This calibrates every positively oriented
    summand in Federer 4.1.12, p. 369. *)
Theorem scalar_current_calibration_test_exists (a b:R):
  exists phi:DT,(forall x,N1 (value phi x)<=1) /\
    forall x,smooth_compact_carrier (scalar_current_compact_interval R a b) x->value phi x=dx.
Proof.
pose K:=scalar_current_compact_interval R a b.
have[gamma [hSupport [hRange hOne]]]:=@current_bounded_neighbourhood_test_exists R h2 1%N K Full
  (@openT (real_norm_metric_space hNX)) (fun _ _=>Logic.I).
pose c:=@current_constant_form R h2 1%N Full hFull 1%N dx.
pose phi:=@current_scalar_cutoff_form_test R h2 1%N 1%N Full hFull c gamma.
have hValue x:value phi x=
    (zero_form_value (@current_test_value R h2 1%N Full hFull 0%N gamma x):R)*:dx.
  rewrite current_scalar_cutoff_form_test_values;last exact:Logic.I.
  by rewrite current_constant_form_values.
exists phi;split.
- move=>x;rewrite hValue (real_seminorm_scale (@current_form_comass_real_norm R h2 1%N 1%N).1).
  have hBounds:0<=zero_form_value (@current_test_value R h2 1%N Full hFull 0%N gamma x)<=1:=hRange x.
  rewrite (ger0_norm (andP hBounds).1).
  have h:=ler_wpM2l (andP hBounds).1 scalar_current_coordinate_comass_le_one.
  rewrite mulr1 in h;exact:le_trans h (andP hBounds).2.
- move=>x hx;rewrite hValue (hOne x hx) zero_formK scale1r;by [].
Qed.
End ScalarCurrentCalibrationTest.
