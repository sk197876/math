(** Federer (1969), 4.1.19, p. 377: each
    original compact smooth divergence pair can be
    tested as two actual full-space compact tests.
    The earlier exact zero extension retains its
    same support and every original point value. *)
From mathcomp Require Import boolp all_boot all_order all_algebra
  functions classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSubspaces
  SmoothTestSpaces SmoothTestEvaluation LinearSubspaceRepresentationUP
  SmoothCurrentDivergence CurrentLipschitzCompactImage
  CompactSummableMultivectors CurrentLonePairImageUP CurrentCompactSmoothDivergenceUP
  CurrentCompactSmoothDivergenceSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactGraphTests.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation V d := (exterior_power X d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation F d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation fv d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hF d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation DT d := (smooth_test_space (hF d)).
Local Notation tv d := (smooth_test_value (hF d)).
Local Notation divF := (@smooth_current_divergence R h2 n m Full hFull).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation E d := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).

(** Source for [current_compact_divergence_graph_tests]:
    the graph tests in the converse smoothing
    argument of Federer 4.1.19, p. 377,
    have exact full-space test representatives. Both
    values vanish outside the same original K,
    including empty K and all exterior degrees. *)
Theorem current_compact_divergence_graph_tests (v : P) :
  @is_current_compact_smooth_divergence_pair R h2 n m U hU v ->
  exists K : smooth_compact_set hNX U, exists a : DT m, exists b : DT m.+1,
    value m v.1=(fun x : UT => tv m a (set_val x)) /\
    value m.+1 v.2=(fun x : UT => tv m.+1 b (set_val x)) /\
    tv m a=fv m (divF (smooth_test_inclusion (hF m.+1) b)) /\
    forall x, ~smooth_compact_carrier K x -> tv m a x=0 /\ tv m.+1 b x=0.
Proof.
move=> [eta [K [hSupport [hLeft hRight]]]].
have hDivSupport := @current_compact_smooth_divergence_support R h2 n m
  U hU K eta hSupport.
have [zeta [hZeta hDivZeta]] :=
  @current_compact_smooth_divergence_zero_extension R h2 n m U hU K eta hSupport.
pose KF := @current_compact_index_in_open R n U Full K (fun _ _ => Logic.I).
have hZetaSupport : @smooth_function_support R X (V m.+1) NX hNX Full
    (F m.+1) (fv m.+1) zeta `<=` smooth_compact_carrier KF.
  apply: (smooth_function_compact_support_iff (hF m.+1) KF zeta).2=> x hx.
  rewrite hZeta; exact: ((smooth_function_compact_support_iff (hE m.+1) K eta).1
    hSupport x hx).
have hDivZetaSupport : @smooth_function_support R X (V m) NX hNX Full
    (F m) (fv m) (divF zeta) `<=` smooth_compact_carrier KF.
  apply: (smooth_function_compact_support_iff (hF m) KF (divF zeta)).2=> x hx.
  rewrite hDivZeta; exact: ((smooth_function_compact_support_iff (hE m) K (div eta)).1
    hDivSupport x hx).
have hZetaMember : smooth_compact_support_subspace (hF m.+1) zeta.
  by exists KF.
have hDivMember : smooth_compact_support_subspace (hF m) (divF zeta).
  by exists KF.
have [b hB] := @subspace_representation_full R (F m.+1) (DT m.+1)
  (smooth_compact_support_subspace (hF m.+1)) (smooth_test_inclusion (hF m.+1))
  (smooth_test_space_laws (hF m.+1)) zeta hZetaMember.
have [a hA] := @subspace_representation_full R (F m) (DT m)
  (smooth_compact_support_subspace (hF m)) (smooth_test_inclusion (hF m))
  (smooth_test_space_laws (hF m)) (divF zeta) hDivMember.
exists K,a,b; split.
- rewrite hLeft; apply: funext=> x.
  change (ev m (div eta) (set_val x)=fv m (smooth_test_inclusion (hF m) a) (set_val x)).
  by rewrite hA hDivZeta.
split.
- rewrite hRight; apply: funext=> x.
  change (ev m.+1 eta (set_val x)=fv m.+1 (smooth_test_inclusion (hF m.+1) b) (set_val x)).
  by rewrite hB hZeta.
split.
- change (fv m (smooth_test_inclusion (hF m) a)=
    fv m (divF (smooth_test_inclusion (hF m.+1) b))).
  by rewrite hA hB.
- move=> x hx; change (fv m (smooth_test_inclusion (hF m) a) x=0 /\
    fv m.+1 (smooth_test_inclusion (hF m.+1) b) x=0).
  rewrite hA hB hDivZeta hZeta; split.
  + exact: ((smooth_function_compact_support_iff (hE m) K (div eta)).1 hDivSupport x hx).
  + exact: ((smooth_function_compact_support_iff (hE m.+1) K eta).1 hSupport x hx).
Qed.
End CompactGraphTests.
