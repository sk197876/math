(** Federer (1969), 4.1.15, p. 373: the actual nonzero
    finite-mass one-current supported at the origin. Its
    point action is the already specified opaque point
    multivector current from 4.1.9. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate
  ExteriorGrading ExteriorPowers FiniteExteriorPowers AlternatingForms
  AlternatingPairing CovectorProducts EuclideanCoordinateForms
  CurrentSpaces CurrentCoefficientNorms CurrentDualNorm RealFunctionalNormUP
  EuclideanTopCurrentMass PointMultivectorCurrentSealed
  PointMultivectorCurrentSupport CurrentSupportGeometry CurrentSupportAgreement
  CurrentMassUP CurrentMassSealed CurrentMassBasic CurrentGlobalComassBound
  CurrentGlobalComassSealed ExtendedSupremumUP ScalarCurrentCalibrationTest
  ScalarCurrentIntervalCompact SmoothCompactSet CurrentIntegrationCriterion
  CurrentFiniteMassRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PointOneCurrent.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation DT:=(@current_test_space R h2 1%N Full hFull 1%N).
Local Notation action:=(@current_value R h2 1%N Full hFull 1%N).
Local Notation value:=(@current_test_value R h2 1%N Full hFull 1%N).
Local Notation support:=(@current_support R h2 1%N Full hFull 1%N).
Local Notation unit:=(e_lambda (@coordinate_basis R 1%N) (ord_tuple 1%N)).
Local Notation e:=(@coordinate_basis R 1%N ord0).
Local Notation dx:=(@euclidean_coordinate_form R 1%N ord0).

(** Source for [point_one_current]: the printed current
    delta_0 wedge e_1 of 4.1.15, p. 373, obtained
    from the existing opaque point multivector current. *)
Definition point_one_current:@current_space R h2 1%N Full hFull 1%N :=
  @PointMultivectorCurrent.value R h2 1%N 1%N Full hFull (0:X) Logic.I unit.
Local Notation T:=point_one_current.

(** Source for [point_one_current_pairing]: the original
    one-vector/one-form pairing in the printed formula for
    T, 4.1.15, p. 373, under the R=R^1 identification. *)
Lemma point_one_current_pairing (phi:A_m X R^o 1%N):
  pairing unit phi=phi [tuple e].
Proof.
rewrite pairing_e_lambda.
congr (phi _);apply:eq_from_tnth=>i.
by rewrite tnth_map tnth_ord_tuple (ord1 i) tnth0.
Qed.

(** Source for [point_one_current_evaluation]: the literal
    T(phi)=<1,phi(0)> assertion of 4.1.15, p. 373,
    on every original compact test one-form. *)
Theorem point_one_current_evaluation (phi:DT):
  action T phi=(value phi 0) [tuple e].
Proof.
rewrite /point_one_current (@PointMultivectorCurrent.laws R h2
  1%N 1%N Full hFull (0:X) Logic.I).
exact:point_one_current_pairing.
Qed.

(** Source for [point_one_current_unit_test]: a previously
    proved unit-comass coordinate test equals DX near the
    origin. It detects the current in 4.1.15, p. 373;
    reuse the actual calibration from 4.1.12. *)
Theorem point_one_current_unit_test:
  exists phi:DT,(forall x,@current_form_comass R h2 1%N 1%N (value phi x)<= 1)
    /\action T phi= 1.
Proof.
have [phi [hUnit hCoordinate]]:=@scalar_current_calibration_test_exists R h2 0 0.
have hOrigin:smooth_compact_carrier (scalar_current_compact_interval R 0 0) (0:X).
  rewrite scalar_current_compact_interval_carrier /= /euclidean_one_project.
  by rewrite ffunE /= lexx.
exists phi;split;first exact:hUnit.
rewrite point_one_current_evaluation (hCoordinate (0:X) hOrigin).
by rewrite euclidean_coordinate_form_dual eqxx.
Qed.

(** Source for [point_one_current_nonzero]: the original
    point-supported one-current in 4.1.15, p. 373, is
    nonzero, as its printed point action requires. *)
Theorem point_one_current_nonzero:T<>0.
Proof.
have [phi [_ hValue]]:=point_one_current_unit_test.
move=>hZero;rewrite hZero (linear0 action) hom_zeroE in hValue.
have hBad:(1:R)=0:=esym hValue.
by have:=@oner_neq0 R;rewrite hBad eqxx.
Qed.

(** Source for [point_one_current_support_subset]: the original
    current vanishes off the origin, supporting the exact
    support assertion of 4.1.15, p. 373. *)
Theorem point_one_current_support_subset:support T `<=` [set (0:X)].
Proof.
exact:(@point_multivector_current_support R h2 1%N 1%N
  Full hFull (0:X) Logic.I unit).
Qed.

(** Source for [point_one_current_support]: the literal
    spt T={0} assertion in 4.1.15, p. 373. *)
Theorem point_one_current_support:support T=[set (0:X)].
Proof.
apply:funext=>x;apply:propext;split;first exact:point_one_current_support_subset.
move=>->;apply:contrapT=>hOutside.
have [phi [_ hValue]]:=point_one_current_unit_test.
have hZero:action T phi=0.
  apply:current_test_disjoint_support_zero=>y hy _.
  have hAt:y=(0:X):=@point_one_current_support_subset y hy.
  exact:(hOutside (eq_ind y (support T) hy (0:X) hAt)).
have hBad:(1:R)=0 by rewrite -hValue;exact:hZero.
by have:=@oner_neq0 R;rewrite hBad eqxx.
Qed.

(** Source for [point_one_current_compact]: the exact
    point support in 4.1.15, p. 373, is compact.
    No flatness or normality is asserted. *)
Theorem point_one_current_compact:
  @compact (real_norm_metric_space hNX) (support T).
Proof.
rewrite point_one_current_support;exact:compact_set1.
Qed.

(** Source for [point_one_current_mass]: the literal
    M(T)= 1 assertion in 4.1.15, p. 373. Its
    upper bound is the old mass/comass duality, and
    its lower bound uses the existing coordinate calibration. *)
Theorem point_one_current_mass:@CurrentMass.value R h2 1%N 1%N Full hFull T= 1%:E.
Proof.
have hUpper:(@CurrentMass.value R h2 1%N 1%N Full hFull T<= 1)%E.
  apply:(extended_supremum_least (@CurrentMass.laws R h2
    1%N 1%N Full hFull T))=>a [phi [hPhi <-]].
  rewrite lee_fin /point_one_current
    (@PointMultivectorCurrent.laws R h2 1%N 1%N Full hFull (0:X) Logic.I).
  have hPair:=real_functional_norm_bound
    (@current_mass_pairing_norm R h2 1%N 1%N unit) (value phi 0).
  rewrite euclidean_top_current_vector_mass_one mul1r in hPair.
  apply:(le_trans (ler_norm _) (le_trans hPair _)).
  exact:((@current_global_comass_bound R h2 1%N 1%N Full
    (value phi) 1).1 hPhi (0:X) Logic.I).
have [phi [hUnit hValue]]:=point_one_current_unit_test.
have hGlobal:(@CurrentGlobalComass.value R h2 1%N 1%N Full (value phi)<= 1)%E.
  apply:(@current_global_comass_bound R h2 1%N 1%N Full (value phi) 1).2.
  by move=>x _;exact:hUnit x.
have hLower:=@current_mass_unit_test_upper R h2 1%N 1%N Full hFull T phi hGlobal.
rewrite hValue in hLower.
apply/eqP;by rewrite eq_le hUpper hLower.
Qed.

(** Source for [point_one_current_finite_mass]: the example
    in 4.1.15, p. 373, has finite original mass. *)
Theorem point_one_current_finite_mass:
  (@CurrentMass.value R h2 1%N 1%N Full hFull T < +oo)%E.
Proof.
rewrite point_one_current_mass;exact:ltry.
Qed.

(** Source for [point_one_current_representable]: finite mass
    of the original example in 4.1.15, p. 373,
    supplies its actual integration representation by 4.1.7. *)
Theorem point_one_current_representable:
  @is_integration_representable_current R h2 1%N 1%N Full hFull T.
Proof.
exact:current_finite_mass_representation point_one_current_finite_mass.
Qed.
End PointOneCurrent.
Arguments point_one_current (R) h2 : clear implicits.
