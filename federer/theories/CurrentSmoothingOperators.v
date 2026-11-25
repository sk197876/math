(** Federer (1969), 4.1.18, pp. 374–375: retain the
    actual smooth/test/distribution smoothing operators of 4.1.2
    for the original current coefficient spaces. All completeness
    and separability hypotheses are discharged by the previously
    proved finite covector laws. No competing current smoothing
    or kernel symmetry is introduced.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentSpaces CurrentEvaluation CurrentPointEvaluation
  SmoothTestSpaces SmoothTestTopology SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  ContinuousRealDual SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP
  SmoothSmoothingFamilyUP SmoothSmoothingFamilySealed TestSmoothingFamilyUP
  TestSmoothingFamilySealed SmoothedDistributionFamilyUP SmoothedDistributionFamilySealed
  DistributionSmoothingTestLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingOperators.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Y:=(A_m X R^o m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation hNY:=(@current_form_comass_real_norm R h2 n m).
Local Notation hY:=(@current_form_complete R h2 n m).
Local Notation hSep:=(@current_form_separable R h2 n m).
Local Notation E:=(@current_smooth_space R h2 n Full hFull m).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation D:=(@current_smooth_derivatives R h2 n Full hFull m).
Local Notation hD:=(@current_smooth_derivative_laws R h2 n Full hFull m).
Local Notation DT:=(@current_test_space R h2 n Full hFull m).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation action:=(@current_value R h2 n Full hFull m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [current_smooth_smoothing]: the original
    Phi_epsilon*omega on actual smooth m-forms, recalled
    in 4.1.18, p. 374, from 4.1.2. *)
Definition current_smooth_smoothing:R->Hom E E:=
  @SmoothSmoothingFamily.value R n Y NY hNY hY hSep E ev hE
    phi hPhi family hFamily.
Local Notation P:=current_smooth_smoothing.
Local Notation hP:=(@SmoothSmoothingFamily.laws R n Y NY hNY hY hSep
  E ev hE phi hPhi family hFamily).

(** Source for [current_test_smoothing]: exactly the same
    convolution on actual compact test m-forms, recalled
    by 4.1.18, p. 374. *)
Definition current_test_smoothing:R->Hom DT DT:=
  @TestSmoothingFamily.value R n Y NY hNY E ev hE
    phi hPhi family hFamily P hP.
Local Notation Q:=current_test_smoothing.
Local Notation hQ:=(@TestSmoothingFamily.laws R n Y NY hNY E ev hE
  phi hPhi family hFamily P hP).

(** Source for [current_smoothing]: the existing T_epsilon
    distribution from 4.1.2, recalled in 4.1.18, p. 374.
    Arbitrary original currents are allowed. *)
Definition current_smoothing (T:C):R->C:=
  @SmoothedDistributionFamily.value R n Y NY hNY hY hSep E ev hE D hD
    phi hPhi family hFamily P hP Q hQ (action T)
    (@continuous_real_dual_member_continuous R DT (smooth_test_opens hE hD)
      (smooth_test_final_topology_laws hE hD).1 T).

(** Source for [current_test_smoothing_inclusion]: the original
    compact-test smoothing is the restriction of the smooth
    form operator, supporting 4.1.18, p. 374. *)
Theorem current_test_smoothing_inclusion epsilon:0<epsilon->forall omega:DT,
  smooth_test_inclusion hE (Q epsilon omega)= P epsilon (smooth_test_inclusion hE omega).
Proof.
exact:hQ.
Qed.

(** Source for [current_smooth_smoothing_convolution]: the actual
    form smoothing retains the literal original convolution
    graph of 4.1.2, as recalled in 4.1.18, p. 374. *)
Theorem current_smooth_smoothing_convolution epsilon:0<epsilon->forall omega:E,
  is_smoothing_convolution hNY (family epsilon) (ev omega) (ev (P epsilon omega)).
Proof.
exact:hP.
Qed.

(** Source for [current_smoothing_action]: the exact original
    T_epsilon(omega)=T(Phi_epsilon*omega) formula recalled
    in 4.1.18, p. 374. *)
Theorem current_smoothing_action (T:C) epsilon:0<epsilon->forall omega:DT,
  action (current_smoothing T epsilon) omega=action T (Q epsilon omega).
Proof.
move=>hEpsilon.
exact:(@SmoothedDistributionFamily.laws R n Y NY hNY hY hSep E ev hE D hD
  phi hPhi family hFamily P hP Q hQ (action T)
  (@continuous_real_dual_member_continuous R DT (smooth_test_opens hE hD)
    (smooth_test_final_topology_laws hE hD).1 T) epsilon hEpsilon).
Qed.

(** Source for [current_smoothing_linear]: smoothing is linear
    on all original currents, supporting the homotopy formula
    in 4.1.18, p. 374. *)
Theorem current_smoothing_linear epsilon:0<epsilon->
  linear (fun T:C=>current_smoothing T epsilon).
Proof.
move=>hEpsilon c S T;apply:(@current_values_extensional R h2 n m Full hFull)=>omega.
rewrite !current_smoothing_action //.
rewrite !(linearP action) !hom_addE !hom_scaleE.
by rewrite !current_smoothing_action.
Qed.

(** Source for [current_smoothing_weak_test_limit]: the original
    weak test limit from 4.1.2 holds for every current,
    as used in the variation squeeze of 4.1.18, p. 375.
    No finite total mass or compact support is required. *)
Theorem current_smoothing_weak_test_limit (T:C) (omega:DT) eta:
  0<eta->exists d:R,0<d /\forall epsilon:R,0<epsilon->epsilon<d->
    `|action (current_smoothing T epsilon) omega-action T omega|<eta.
Proof.
move=>hEta.
have [d [hd hNear]]:=@distribution_smoothing_test_limit R n Y NY hNY hY hSep
  E ev hE D hD phi hPhi family hFamily P hP Q hQ (action T)
  (@continuous_real_dual_member_continuous R DT (smooth_test_opens hE hD)
    (smooth_test_final_topology_laws hE hD).1 T) omega eta hEta.
exists d;split;first exact:hd.
move=>epsilon hEpsilon hSmall;rewrite current_smoothing_action //.
exact:hNear epsilon hEpsilon hSmall.
Qed.
End CurrentSmoothingOperators.
Arguments current_smooth_smoothing (R) h2 n m phi family hPhi hFamily : clear implicits.
Arguments current_test_smoothing (R) h2 n m phi family hPhi hFamily : clear implicits.
Arguments current_smoothing (R) h2 n m phi family hPhi hFamily T epsilon : clear implicits.
