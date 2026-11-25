(** Federer (1969), 4.1.12, p. 367: a
    real linear functional with finite F_K is an
    actual current for the original test topology.
    Reuse the same-compact distribution criterion and
    the preceding order-one flat-form bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothFunctionSupport SmoothDerivativeSeminormUP
  SmoothDerivativeSeminormLaws SmoothDerivativeSupport SmoothTestSpaces LinearSubspaceRepresentationUP
  RealSeminormOperations SeminormRealDualBound DistributionLocalBound OpenFamilyTopologyUP NormOpenTopology
  SmoothTestTopology ContinuousRealDual CurrentFlatFormSeminormLaws CurrentFlatFormOrderBound
  CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFlatFiniteContinuity.
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

(** Source for [current_finite_flat_functional_continuous]:
    finite F_K(T) implies continuity for the literal
    original test topology, the first observation of
    Federer 4.1.12, p. 367. Every original fixed-
    support step retains its own compact set. *)
Theorem current_finite_flat_functional_continuous (T:Hom DT R^o):
  (Dual T < +oo)%E->open_family_continuous (@current_test_opens R h2 n U hU m) RO T.
Proof.
move=>hFinite.
have [a [ha hValue]]:=@current_flat_dual_finite_value R h2 n m U hU K T hFinite.
have hBound:=@current_flat_dual_finite_bound R h2 n m U hU K T a hValue.
have [C [hC hOrder]]:=@current_flat_form_order_one_bound R h2 n m U hU K.
apply:(@distribution_continuity_local_bound R X Y NX NY hNX hNY U hU E ev hE D hD T).2=>L.
pose pL:=fun phi:DK L=>nu L 1%N (fixed L phi).
pose TL:=hom_comp T (step L).
have hpL:is_real_seminorm pL.
  exact:(@real_seminorm_linear_precompose R (DK L) E (nu L 1%N)
    (smooth_derivative_seminorm_is_seminorm (smooth_function_derivative_seminorm_laws hD L 1%N))
    (fixed L) (hom_linear (fixed L))).
have hStepBound:forall phi:DK L,`|TL phi|<=(a * C) * pL phi.
  move=>phi;rewrite /TL hom_compE /pL.
  have hSupport:=subspace_representation_member (smooth_fixed_test_space_laws hE L) phi.
  have hCompact:=@smooth_supported_seminorm_bound R X Y NX NY hNX hNY U hU E ev hE D hD
    L K 1%N (nu L 1%N) (nu K 1%N)
    (smooth_function_derivative_seminorm_laws hD L 1%N)
    (smooth_function_derivative_seminorm_laws hD K 1%N) (fixed L phi) hSupport.
  have hFlat:Flat (step L phi)<=C * nu L 1%N (fixed L phi).
    rewrite /current_flat_test_seminorm smooth_test_step_evaluation.
    exact:(le_trans (hOrder (fixed L phi)) (ler_wpM2l hC hCompact)).
  have h:=le_trans (hBound (step L phi)) (ler_wpM2l ha hFlat).
  by rewrite mulrA in h.
have [M hInteger]:=@seminorm_bound_integer_constant R (DK L) pL hpL TL (a * C)
  (mulr_ge0 ha hC) hStepBound.
exists 1%N,M;move=>phi.
exact:hInteger phi.
Qed.

(** Source for [current_finite_flat_functional_represents]:
    every algebraic finite-flat functional is represented
    by an actual original current, Federer 4.1.12,
    p. 367. The actual dual's fullness supplies the
    representative; continuity is a proved conclusion. *)
Theorem current_finite_flat_functional_represents (T:Hom DT R^o):
  (Dual T < +oo)%E->exists S:@current_space R h2 n U hU m,
    @current_value R h2 n U hU m S=T.
Proof.
move=>hFinite.
exact:(@continuous_real_dual_represents R DT (@current_test_opens R h2 n U hU m)
  (smooth_test_final_topology_laws hE hD).1 T
  (current_finite_flat_functional_continuous hFinite)).
Qed.
End CurrentFlatFiniteContinuity.
