(** Federer (1969), 4.1.7, p. 359: the
    original point mass has support at its
    point and finite normal mass. These
    supporting consequences make the boundary
    and support obstruction in the in-book
    half-line example concrete. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentCoefficientNorms CurrentSpaces
  CurrentDirac CurrentEvaluation CurrentSupportGeometry CurrentSupportAgreement CurrentScalarCutoffs
  CurrentZeroCovectorMaps CurrentMassUP CurrentMassSealed CurrentGlobalComassBound CurrentFiniteMassRepresentation
  NormalCurrentsUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestEvaluation
  ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DiracCurrentBounds.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU 0%N).
Local Notation DT := (@current_test_space R h2 n U hU 0%N).
Local Notation action := (@current_value R h2 n U hU 0%N).
Local Notation value := (@current_test_value R h2 n U hU 0%N).
Local Notation delta := (@dirac_current R h2 n U hU).
Local Notation support := (@current_support R h2 n U hU 0%N).
Variable c:X.
Hypothesis hc:U c.

(** Source for [dirac_current_unit_test]: an actual
    scalar test has delta_c value one,
    supporting the original point evaluation in
    Federer 4.1.7, p. 359. *)
Theorem dirac_current_unit_test:exists gamma:DT,action (delta c) gamma = 1.
Proof.
have hIn:[set c] `<=` U by move=>x ->;exact:hc.
pose K:=@Build_smooth_compact_set R X NX hNX U [set c] hIn (@compact_set1 (real_norm_metric_space hNX) c).
have[gamma [W [hW [hKW [hWU hOne]]]]]:=@current_compact_scalar_cutoff R h2 n U hU K.
exists gamma;rewrite dirac_current_evaluation (hOne c (hKW c (erefl c))).
exact:zero_formK.
Qed.

(** Source for [dirac_current_support_subset]: the
    original point current is supported at c,
    supporting the half-line example of
    Federer 4.1.7, p. 359. *)
Theorem dirac_current_support_subset:support (delta c) `<=` [set c].
Proof.
have hIn:[set c] `<=` U by move=>x ->;exact:hc.
pose K:=@Build_smooth_compact_set R X NX hNX U [set c] hIn (@compact_set1 (real_norm_metric_space hNX) c).
apply:(@current_support_compact_criterion R h2 n 0%N U hU K (delta c)).2=>psi hPsi.
have hZero:value psi c=0.
  apply:contrapT=>hNo.
  have hSupp:=@smooth_function_nonzero_in_support R X (A_m X R^o 0) NX hNX U DT value psi c hc hNo.
  exact:(hPsi c hSupp).2 (erefl c).
by rewrite dirac_current_evaluation hZero linear0.
Qed.

(** Source for [dirac_current_support]: the original
    point current has support exactly {c},
    supporting the actual support obstruction
    in Federer 4.1.7, p. 359. *)
Theorem dirac_current_support:support (delta c)=[set c].
Proof.
apply:funext=>x;apply:propext;split;first exact:dirac_current_support_subset.
move=>->;apply:contrapT=>hOutside.
have[gamma hGamma]:=dirac_current_unit_test.
have hZero:action (delta c) gamma=0.
  apply:current_test_disjoint_support_zero=>y hy _.
  have heq:y=c:=@dirac_current_support_subset y hy.
  exact:(hOutside (eq_ind y (support (delta c)) hy c heq)).
have hBad:(1:R)=0 by rewrite -hGamma;exact:hZero.
by have:=@oner_neq0 R;rewrite hBad eqxx.
Qed.

(** Source for [dirac_current_finite_mass]: the
    original point current has mass at
    most one and hence finite mass,
    supporting Federer 4.1.7, p. 359. *)
Theorem dirac_current_finite_mass:
  (@CurrentMass.value R h2 n 0%N U hU (delta c)<=1)%E /\
  (@CurrentMass.value R h2 n 0%N U hU (delta c) < +oo)%E.
Proof.
have hBound:(@CurrentMass.value R h2 n 0%N U hU (delta c)<=1)%E.
  apply:(extended_supremum_least (@CurrentMass.laws R h2 n 0%N U hU (delta c)))=>a [psi [hPsi <-]].
  rewrite lee_fin dirac_current_evaluation.
  apply:le_trans (ler_norm _) _.
  change (`|@current_zero_form_coefficient R n (value psi c)|<=1).
  rewrite -current_zero_form_coefficient_norm.
  exact:(@current_global_comass_bound R h2 n 0%N U (value psi) 1).1 hPsi c hc.
split=>//;exact:le_lt_trans hBound (ltry 1).
Qed.

(** Source for [dirac_current_normal]: the original
    unit point mass is a normal
    zero-current, supporting the boundary assertion
    in Federer 4.1.7, p. 359. *)
Theorem dirac_current_normal:@is_normal_current R h2 n U hU 0%N (delta c).
Proof.
split.
- split;last by [].
  exact:(@current_finite_mass_representation R h2 n 0%N U hU (delta c) dirac_current_finite_mass.2).
- rewrite dirac_current_support;exact:compact_set1.
Qed.
End DiracCurrentBounds.
