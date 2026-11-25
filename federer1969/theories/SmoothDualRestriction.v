(** Federer (1969), 4.1.1, p. 345: the natural continuous
    linear monomorphism E'(U,Y) to D'(U,Y). Its existence
    and weak continuity use the actual test inclusion;
    injectivity follows from compact cutoff replacement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP NormOpenTopology LinearSubspaceRepresentationUP SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces
  SmoothTestTopology SmoothCutoffReplacement SmoothDualFiniteBound ContinuousRealDual
  ContinuousRealDualTranspose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothDualRestriction.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation EO := (smooth_function_opens hD).
Local Notation hEO := (smooth_function_topology_laws hD).1.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation ED := (@continuous_real_dual_space R E EO hEO).
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eE := (@continuous_real_dual_evaluation R E EO hEO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation EWO := (@continuous_real_dual_weak_opens R E EO hEO).
Local Notation DWO := (@continuous_real_dual_weak_opens R DT SO hSO).
Local Notation hInc := (@smooth_test_inclusion_continuous R X Y NX NY hNX hNY U E ev hE D hD).

(** Source for [smooth_dual_test_restriction]: the actual
    dual map obtained by restricting a continuous functional
    to D(U,Y), Federer 4.1.1, p. 345. *)
Definition smooth_dual_test_restriction:Hom ED DD:=
  @continuous_real_dual_transpose R DT E SO EO hSO hEO inc hInc.

(** Source for [smooth_dual_test_restriction_evaluation]: the
    restriction evaluates T on the included test function,
    Federer 4.1.1, p. 345. *)
Lemma smooth_dual_test_restriction_evaluation T f:
  eD (smooth_dual_test_restriction T) f=eE T (inc f).
Proof. exact:continuous_real_dual_transpose_evaluation. Qed.

(** Source for [smooth_dual_test_restriction_weak_continuous]:
    the natural map E' to D' is continuous for their weak
    topologies, Federer 4.1.1, p. 345. *)
Theorem smooth_dual_test_restriction_weak_continuous:
  open_family_continuous EWO DWO smooth_dual_test_restriction.
Proof. exact:continuous_real_dual_transpose_weak_continuous. Qed.

Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.

(** Source for [continuous_smooth_functional_cutoff_agreement]:
    a single compact cutoff preserves all evaluations of a
    continuous functional on E, supporting the monomorphism
    in Federer 4.1.1, p. 345, by the bound on p. 344. *)
Theorem continuous_smooth_functional_cutoff_agreement (L:Hom E R^o):
  open_family_continuous EO (norm_open_family (@scalar_absolute_value_norm R)) L ->
  exists K:smooth_compact_set hNX U,forall f,
    L (inc (@smooth_cutoff_replacement R X Y NX NY hNX hNY n b hb U hU E ev hE K f))=L f.
Proof.
move=>hL.
have [i [K [C [hC hbL]]]]:=(smooth_dual_finite_bound hD L).1 hL.
exists K=>f.
have hDiff:=@smooth_cutoff_replacement_seminorm_difference R X Y NX NY hNX hNY n b hb U hU
  E ev hE D hD K i f.
have hBound:=hbL (inc (@smooth_cutoff_replacement R X Y NX NY hNX hNY n b hb U hU E ev hE K f)-f).
rewrite hDiff mulr0 linearB in hBound.
apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le hBound normr_ge0; reflexivity.
Qed.

(** Source for [continuous_smooth_functional_determined_by_tests]:
    a continuous real linear functional on E that vanishes
    on D vanishes everywhere, supporting the injectivity in
    Federer 4.1.1, p. 345. *)
Theorem continuous_smooth_functional_determined_by_tests (L:Hom E R^o):
  open_family_continuous EO (norm_open_family (@scalar_absolute_value_norm R)) L ->
  (forall f:DT,L (inc f)=0) ->L=0.
Proof.
move=>hL hz; have [K hK]:=continuous_smooth_functional_cutoff_agreement hL.
apply:hom_ext=>f; change (L f=0).
rewrite -(hK f); exact:hz.
Qed.

(** Source for [smooth_dual_test_restriction_injective]: the
    natural continuous linear map E' to D' is injective,
    Federer 4.1.1, p. 345. No source-dimension exception
    is required for this assertion. *)
Theorem smooth_dual_test_restriction_injective:injective smooth_dual_test_restriction.
Proof.
move=>T S he.
have hZero:eE (T-S)=0.
  apply:continuous_smooth_functional_determined_by_tests.
  - exact:continuous_real_dual_member_continuous.
  - move=>f.
    have hEval:=congr1 (fun Q:DD=>eD Q f) he.
    rewrite !smooth_dual_test_restriction_evaluation in hEval.
    rewrite linearB.
    change (eE T (inc f)-eE S (inc f)=0).
    by rewrite hEval subrr.
have hTS:T-S=0.
  apply:(subspace_representation_injective (@continuous_real_dual_model_laws R E EO hEO)).
  by rewrite hZero linear0.
by apply/eqP; rewrite -subr_eq0 hTS eqxx.
Qed.
End SmoothDualRestriction.
