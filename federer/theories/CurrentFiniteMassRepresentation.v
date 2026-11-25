(** Federer (1969), 4.1.7, p. 358: finite
    mass implies representability by integration.
    Follow the original application of 4.1.5:
    a compact scalar majorant has a finite
    uniform bound, and the earlier positive-scale
    mass estimate bounds its entire test gauge. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain DistributionVariationUP
  DistributionVariationFinite DistributionVariationBoundedExistence FunctionLatticeUP CompactSupportFunctionUP
  UniformFunctionNormUP UniformFunctionNorm CurrentIntegrationCriterion CurrentMassSealed CurrentMassBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFiniteMassRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := [the topologicalType of set_type (U:set (real_norm_metric_space hNX))].
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNX) U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).

(** Source for [current_finite_mass_representation]:
    if M(T)<infinity then T is representable
    by integration, Federer 4.1.7, p. 358,
    paragraph after the mass definitions. The
    actual Radon representation retains the original
    test topology and every original domain. *)
Theorem current_finite_mass_representation (T:C):
  (M T < +oo)%E->@is_integration_representable_current R h2 n m U hU T.
Proof.
move=>hFinite.
have[b [hb hValue]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have hMass:=@current_mass_majorant_one R h2 n m U hU T.
rewrite hValue in hMass.
apply:(@current_integration_finite_gauge_criterion R h2 n m U hU T).1=>f hf.
pose B:=@compact_support_uniform_norm R UT f.
have hBSpec:=@compact_support_uniform_norm_specification R UT f hf.1.
have hB:0<=B:=uniform_function_norm_nonnegative hBSpec.
pose a:=B+1.
have ha:0<a by rewrite /a;lra.
apply:(@distribution_variation_bounded_value_exists R UT Y NY hNY DT dvalues
  (action T) f (a*b) hf.2)=>phi hPhi.
have hScaled (x:UT):@current_form_comass R h2 n m (dvalues phi x)<=a*1.
  have hF:f x<=B:=le_trans (ler_norm _) (uniform_function_norm_bound hBSpec x).
  rewrite mulr1;have hStep:B<=a by rewrite /a;lra.
  exact:le_trans (hPhi x) (le_trans hF hStep).
have hBound:=@distribution_variation_finite_scaled_bound R UT Y NY hNY DT dvalues
  (action T) (fun _=>1) b a hMass ha phi hScaled.
exact:le_trans (ler_norm _) hBound.
Qed.
End CurrentFiniteMassRepresentation.
