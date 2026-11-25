(** Federer (1969), 4.1.7, p. 357: constant
    Lebesgue-density currents restricted to the
    original open U. Their action uses the
    literal integral over U, as in
    the original constancy theorem of 4.1.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import CurrentCoefficientNorms Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingIsomorphism AlternatingPairing
  CurrentSpaces CurrentDensityUP CurrentDensityAction CurrentConstantDensity CurrentOpenRestriction
  SmoothTestSpaces SmoothTestEvaluation SummableRealFunctionUP MeasureSubsetIntegral RealSubsetIntegralGraph
  EuclideanLebesgueDimensions FiniteExteriorPowers EuclideanFundamentalCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentOpenConstantDensity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation hUF := (fun x (_:U x)=>Logic.I).
Local Notation P := (@current_open_test_extension R h2 n m U (fun _=>True) hU hFull hUF).
Local Notation Q := (@current_open_restriction R h2 n m U (fun _=>True) hU hFull hUF).

(** Source for [current_open_constant_density]: the
    original constant Lebesgue-density current on
    U as an actual linear map of
    its multivector, supporting Federer 4.1.7,
    p. 357. *)
Definition current_open_constant_density:Hom (exterior_power X m) (@current_space R h2 n U hU m):=
  hom_comp Q (@current_constant_density_map R h2 n m).

(** Source for [current_open_constant_density_action]:
    the original action is the literal
    Lebesgue integral over U of the
    constant-vector pairing, supporting the
    constancy theorem in Federer 4.1.7,
    p. 357. *)
Theorem current_open_constant_density_action a psi:
  is_measure_subset_integral (@euclidean_lebesgue_measure R n) U
    (real_total_integrand (fun x=>pairing a (@current_test_value R h2 n U hU m psi x)))
    (@current_value R h2 n U hU m (current_open_constant_density a) psi)%:E.
Proof.
rewrite /current_open_constant_density hom_compE current_open_restriction_evaluation.
have h:=@current_constant_density_action R h2 n m a (P psi).
have hEq:(fun x=>pairing a (@current_test_value R h2 n (fun _=>True) hFull m (P psi) x))=
    (fun x=>pairing a (@current_test_value R h2 n U hU m psi x)).
  apply:funext=>x;by rewrite current_open_test_extension_values.
rewrite hEq in h.
apply:(@real_subset_integral_total R X (@euclidean_lebesgue_measure R n) U
  (fun x=>pairing a (@current_test_value R h2 n U hU m psi x))
  (fun x=>pairing a (@current_test_value R h2 n U hU m psi x)) _
  (fun _ _=>erefl) _).2;last exact:h.
move=>x hx.
have hZero:@current_test_value R h2 n U hU m psi x=0.
  exact:(@smooth_test_value_outside R X (A_m X R^o m) NX
    (@current_form_comass R h2 n m) (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@current_form_comass_real_norm R h2 n m) U (@current_smooth_space R h2 n U hU m)
    (@current_smooth_value R h2 n U hU m) (@current_smooth_space_laws R h2 n U hU m) psi x hx).
by rewrite hZero /pairing linear0 hom_zeroE.
Qed.
End CurrentOpenConstantDensity.

(** Source for [euclidean_fundamental_current_open]:
    the original E^n restricted to U,
    Federer 4.1.7, p. 357, in
    the constancy theorem's support conclusion. *)
Definition euclidean_fundamental_current_open (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x):
    @current_space R h2 n U hU n:=
  @current_open_constant_density R h2 n n U hU (e_lambda (@coordinate_basis R n) (ord_tuple n)).

(** Source for [euclidean_fundamental_current_open_restriction]:
    the preceding current is exactly the
    original open restriction of E^n,
    supporting Federer 4.1.7, p. 357. *)
Theorem euclidean_fundamental_current_open_restriction (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x):
  @euclidean_fundamental_current_open R h2 n U hU=
  @current_open_restriction R h2 n n U (fun _=>True) hU
    (fun x (_:True)=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x)
    (fun _ _=>Logic.I) (@euclidean_fundamental_current R h2 n).
Proof. by []. Qed.
