(** Federer (1969), 4.1.7, pp. 357, 359:
    constant Lebesgue densities are determined
    by their actual currents on every
    nonempty open domain. Reuse the fixed
    unit-test uniqueness of 4.1.4,
    pp. 348–349; no new bump argument
    or density uniqueness theorem is assumed. *)
From mathcomp Require Import boolp all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import NormBoundedLinearTopology Hom RealNormUP NormMetric NormDifferentialUP NormOpenTopology
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingIsomorphism AlternatingPairing CurrentCoefficientNorms CurrentCoefficientCompleteness
  CurrentSpaces CurrentSupportGeometry CurrentMultivectorDual MultivectorDualUP MultivectorDualSealed ContinuousDualUP
  CurrentConstantDensity CurrentOpenConstantDensity DomainConstantFunctionalUniqueness
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation EuclideanLebesgueDimensions
  MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP RealSubsetIntegralGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentConstantDensityUniqueness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation V := (exterior_power X m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [current_constant_pairing_density_unique]:
    two constant densities representing the
    same original current on a nonempty
    open domain are equal, the fixed-test
    consequence used in Federer 4.1.7,
    pp. 357, 359. *)
Theorem current_constant_pairing_density_unique (T:C) (a b:V):
  (exists x,U x)->
  (forall psi,is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun x=>pairing a (value psi x))) (action T psi)%:E)->
  (forall psi,is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun x=>pairing b (value psi x))) (action T psi)%:E)->a=b.
Proof.
move=>[x hx] hA hB.
pose alpha:=@MultivectorDual.evaluation R X m a.
pose beta:=@MultivectorDual.evaluation R X m b.
have hOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>z hz;exact:(@norm_domain_interior_neighbourhood R X NX hNX U z).1 (hU z hz).
have hRepA psi:(@current_test_support R h2 n m U hU psi `<=` U)->
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (real_total_integrand (fun z=>alpha (value psi z))) (action T psi)%:E.
  move=>_;have hEq:(fun z=>alpha (value psi z))=(fun z=>pairing a (value psi z)).
    apply:funext=>z;exact:MultivectorDual.laws.
  by rewrite hEq;exact:hA.
have hRepB psi:(@current_test_support R h2 n m U hU psi `<=` U)->
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (real_total_integrand (fun z=>beta (value psi z))) (action T psi)%:E.
  move=>_;have hEq:(fun z=>beta (value psi z))=(fun z=>pairing b (value psi z)).
    apply:funext=>z;exact:MultivectorDual.laws.
  by rewrite hEq;exact:hB.
have hSame:=@domain_constant_functional_unique R n Y NY hNY (@current_form_complete R h2 n m)
  U hU E ev hE U hOpen (fun _ hz=>hz) x hx (action T) alpha beta
  (@continuous_dual_continuous R Y NY hNY V (@MultivectorDual.evaluation R X m)
    (@current_vector_mass R h2 n m) hDual a)
  (@continuous_dual_continuous R Y NY hNY V (@MultivectorDual.evaluation R X m)
    (@current_vector_mass R h2 n m) hDual b) hRepA hRepB.
exact:(continuous_dual_injective hDual hSame).
Qed.

(** Source for [current_open_constant_density_injective]:
    the actual original constant-density map
    is injective on a nonempty open
    domain, supporting Federer 4.1.7,
    pp. 357, 359. *)
Theorem current_open_constant_density_injective:(exists x,U x)->
  injective (@current_open_constant_density R h2 n m U hU).
Proof.
move=>hNonempty a b hEqual.
have hTotal c psi:is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun x=>pairing c (value psi x)))
    (action (@current_open_constant_density R h2 n m U hU c) psi)%:E.
  have hOff:forall x,~U x->pairing c (value psi x)=0.
    move=>x hx.
    have hZero:value psi x=0:=
      @smooth_test_value_outside R X Y NX NY hNX hNY U E ev hE psi x hx.
    by rewrite hZero /pairing linear0 hom_zeroE.
  exact:((@real_subset_integral_total R X (@euclidean_lebesgue_measure R n) U
    (fun x=>pairing c (value psi x)) (fun x=>pairing c (value psi x)) _
    (fun _ _=>erefl) hOff).1 (@current_open_constant_density_action R h2 n m U hU c psi)).
apply:(current_constant_pairing_density_unique hNonempty (hTotal a))=>psi.
by rewrite hEqual;exact:hTotal.
Qed.
End CurrentConstantDensityUniqueness.

(** Source for [current_constant_density_injective]:
    whole-space constant densities are determined
    by their original currents, supporting the
    constancy and primitive statements of Federer
    4.1.7, pp. 357, 359. *)
Theorem current_constant_density_injective (R:realType) (h2:(1+1:R)!=0) n m:
  injective (@current_constant_density R h2 n m).
Proof.
move=>a b hEqual.
apply:(@current_constant_pairing_density_unique R h2 n m (fun _=>True)
  (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x)
  (@current_constant_density R h2 n m a) a b (ex_intro _ 0 Logic.I)
  (@current_constant_density_action R h2 n m a))=>psi.
by rewrite hEqual;exact:current_constant_density_action.
Qed.
