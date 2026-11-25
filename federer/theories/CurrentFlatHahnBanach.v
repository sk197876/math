(** Federer (1969), 4.1.12, p. 367: the
    actual original graph map in the two test
    spaces admits the printed Hahn–Banach extension.
    Its product seminorm keeps exactly the original K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothFunctionSupport SmoothDerivativeSeminormUP
  SmoothDerivativeSeminormLaws SmoothDerivativeSupport SmoothTestSpaces LinearSubspaceRepresentationUP
  RealSeminormOperations SeminormRealDualBound DistributionLocalBound OpenFamilyTopologyUP NormOpenTopology
  SmoothTestTopology ContinuousRealDual CurrentFlatFormSeminormLaws CurrentFlatFormOrderBound
  CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic CurrentTestExteriorDerivative
  SeminormGraphPairExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFlatHahnBanach.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation DK := (smooth_fixed_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation fixed := (smooth_fixed_test_inclusion hE).
Local Notation step := (smooth_test_step hE).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation Flat := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation Dual := (@CurrentFlatDualSeminorm.value R h2 n m U hU K).
Local Notation RO := (norm_open_family (@scalar_absolute_value_norm R)).

Local Notation Next := (@current_smooth_space R h2 n U hU m.+1).
Local Notation NT := (@current_test_space R h2 n U hU m.+1).
Local Notation hNextE := (@current_smooth_space_laws R h2 n U hU m.+1).
Local Notation hNextD := (@current_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation incNext := (smooth_test_inclusion hNextE).
Local Notation nuNext := (smooth_function_derivative_seminorm hNextD).
Local Notation p := (fun phi:DT=>nu K 0%N (inc phi)).
Local Notation q := (fun psi:NT=>nuNext K 0%N (incNext psi)).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).

(** Source for [current_flat_hahn_banach_extension]: the
    original L on D^m(U) times D^(m+1)(U) agrees
    with T on (phi,d phi) and is dominated by
    F_K(T) times the original product seminorm,
    Federer 4.1.12, pp. 367–368. The displayed
    constant is the exact finite flat value. *)
Theorem current_flat_hahn_banach_extension (T:Hom DT R^o) c:
  Dual T=c%:E->
  exists L:Hom [the lmodType R of (DT * NT)%type] R^o,
    (forall phi,L (phi,d phi)=T phi) /\
    forall phi psi,`|L (phi,psi)|<=c * Num.max (p phi) (q psi).
Proof.
move=>hValue.
have hc:=@current_flat_dual_nonnegative R h2 n m U hU K T.
rewrite hValue lee_fin in hc.
have hp:is_real_seminorm p.
  exact:(@real_seminorm_linear_precompose R DT E (nu K 0%N)
    (smooth_derivative_seminorm_is_seminorm (smooth_function_derivative_seminorm_laws hD K 0%N))
    inc (hom_linear inc)).
have hq:is_real_seminorm q.
  exact:(@real_seminorm_linear_precompose R NT Next (nuNext K 0%N)
    (smooth_derivative_seminorm_is_seminorm (smooth_function_derivative_seminorm_laws hNextD K 0%N))
    incNext (hom_linear incNext)).
apply:(@seminorm_graph_pair_extension R DT NT p q hp hq d T c hc)=>phi.
have hGraphNorm:Num.max (p phi) (q (d phi))=Flat phi.
  by rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula
    current_test_exterior_derivative_inclusion.
rewrite hGraphNorm.
exact:(@current_flat_dual_finite_bound R h2 n m U hU K T c hValue phi).
Qed.
End CurrentFlatHahnBanach.
