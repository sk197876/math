(** Federer (1969), 4.1.1, p. 345: a distribution
    annihilates every test whose support misses its support.
    The proof follows the preceding partition decomposition,
    using actual original test multipliers and compact
    incidence. The local argument also holds for arbitrary
    real linear functionals on the test space. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormRegularityOperations
  LinearBasis CompactSupportFunctionUP SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces
  SmoothTestEvaluation SmoothCompactPartitionUP FiniteNormSmoothPartitionExistence
  SmoothPartitionCompactSelection SmoothMultiplierUP SmoothTestScalarMultiplier
  SmoothTestFiniteDecomposition FunctionalSupportUP SmoothTestAnnihilationCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestFunctionalSupport.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation XN := (real_norm_metric_space hNX).
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT value).
Local Notation tsupport := (@smooth_functional_support R X Y NX hNX U DT value).

(** Source for [smooth_test_functional_disjoint_support_zero]:
    T(phi)=0 if spt T and spt phi are disjoint,
    Federer 4.1.1, p. 345. The original function supports
    and local annihilation definition determine both sides. *)
Theorem smooth_test_functional_disjoint_support_zero (T:Hom DT R^o) f:
  (forall x,tsupport T x ->~support f x) ->T f=0.
Proof.
move=>hDisjoint.
have [Phi [hOpen [hDomain hPhi]]]:=
  @smooth_test_disjoint_annihilation_cover R X Y NX NY hNX hNY U hU E ev hE T f hDisjoint.
have [J [I [v [hCount [hv hRef]]]]]:=
  @finite_norm_smooth_partition_exists R X NX hNX n b hb Phi hOpen.
rewrite hDomain in hv.
have [K hK]:=smooth_test_support_bound hE f.
have [F [hFI hInactive]]:=smooth_partition_compact_active_selection hv K.
pose hScalar (s:F) k:=@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) (fun _=>True) U (v (val s)) k (fun _ _=>Logic.I) hU
  (@smooth_partition_global_class R X NX hNX U J I v hv (val s) (@hFI (val s) (valP s)) k).
pose P (s:F):Hom DT DT:=@smooth_test_scalar_multiplier R X Y NX NY hNX hNY U E ev hE
  (v (val s)) (hScalar s).
have hP s:is_smooth_multiplier U value (v (val s)) (P s).
  exact:(@smooth_test_scalar_multiplier_laws R X Y NX NY hNX hNY U E ev hE
    (v (val s)) (hScalar s)).
have hSum:=@smooth_test_finite_partition_identity R X Y NX NY hNX hNY U E ev hE J I v hv
  K F hFI hInactive P hP f hK.
rewrite -hSum linear_sum; apply:big1=>s _.
have [W [hW hSW]]:=hRef (val s) (@hFI (val s) (valP s)).
have [hWU [hAnn|hZero]]:=hPhi W hW.
- apply:hAnn.2=>x hx.
  apply:hSW.
  exact:(@smooth_test_scalar_multiplier_support R X Y NX NY hNX hNY U E ev hE
    (v (val s)) (hScalar s) f x hx).
- have hProduct:P s f=0.
    apply:(smooth_test_values_extensional hE)=>x hx.
    have hEval:=hP s f x hx.
    have hValue0:value 0 x=0:=congr1 (fun q:X->Y=>q x) (linear0 (smooth_test_values_hom hE)).
    rewrite hValue0 hEval.
    case:(pselect (W x))=>[hWx|hWx].
    + by rewrite (hZero x hWx) scaler0.
    + have hWeight:v (val s) x=0.
        apply:(@real_function_zero_off_support R XN (v (val s)) x)=>hs.
        exact:hWx (hSW x hs).
      by rewrite hWeight scale0r.
  by rewrite hProduct linear0.
Qed.
End TestFunctionalSupport.
