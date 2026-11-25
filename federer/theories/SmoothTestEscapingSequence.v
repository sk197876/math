(** Federer (1969), 4.1.1, p. 344: compact tests
    can escape each compact support while converging
    to zero in E. This proves the corrected
    nonembedding statement for a noncompact domain
    and a nonzero target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP LinearBasis
  ContinuousMultilinearSealed OpenFamilyConvergence SmoothCompactSet SmoothCompactExhaustionUP
  SmoothCompactExhaustionSealed SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP
  SmoothFunctionSupport SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothLocalSupport
  LinearSubspaceRepresentationUP SmoothTestSpaces SmoothTestEvaluation SmoothTestEscapingPoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EscapingSequence.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT value).
Local Notation K := (@SmoothCompactExhaustion.value R X NX hNX d b hb U hU).
Local Notation hK := (@SmoothCompactExhaustion.laws R X NX hNX d b hb U hU).

(** Source for [smooth_test_escaping_sequence_exists]: actual
    tests tending to zero in E eventually avoid
    every D_L, supporting the corrected nonembedding
    assertion in Federer 4.1.1, p. 344. *)
Theorem smooth_test_escaping_sequence_exists:
  ~compact [set x:real_norm_metric_space hNX|U x] ->
  (exists y:Y,y<>0) ->
  exists s:nat->DT,(forall n,s n<>0) /\
    open_family_converges (smooth_function_opens hD) ((fun n=>inc (s n)) @ \oo) (inc 0) /\
    (forall L:smooth_compact_set hNX U,exists N,forall n,(N<=n)%N ->
      forall f:smooth_fixed_test_space hE L,smooth_test_step hE L f<>s n).
Proof.
move=>hNoncompact [y hy].
have hPoint n:exists a:X,U a /\ ~smooth_compact_carrier (K n) a.
  case:(pselect (exists a:X,U a /\ ~smooth_compact_carrier (K n) a))=>// hn.
  apply:False_ind; apply:hNoncompact.
  have hEq:[set x:real_norm_metric_space hNX|U x]=[set x|smooth_compact_carrier (K n) x].
    apply:funext=>x; apply:propext; split.
    - move=>hx; case:(pselect (smooth_compact_carrier (K n) x))=>// hNo.
      apply:False_ind; apply:hn; by exists x.
    - exact:(smooth_compact_in_domain (K n) x).
  rewrite hEq; exact:smooth_compact_is_compact.
have hPair n:exists af:X*DT,U af.1 /\ ~smooth_compact_carrier (K n) af.1 /\
    value af.2 af.1=y /\ support af.2 `<=` (U `&` ~` smooth_compact_carrier (K n)).
  have [a [ha hNo]]:=hPoint n.
  have [f [hf hs]]:=@smooth_test_escaping_point_exists R X Y NX NY hNX hNY d b hb U hU E ev hE
    (K n) a y ha hNo.
  by exists (a,f).
pose af n:=projT1 (cid (hPair n)).
have hAf n:U (af n).1 /\ ~smooth_compact_carrier (K n) (af n).1 /\
    value (af n).2 (af n).1=y /\ support (af n).2 `<=` (U `&` ~` smooth_compact_carrier (K n)).
  exact:(projT2 (cid (hPair n))).
pose s n:=(af n).2.
have hNe n:s n<>0.
  move=>he; have hv: value (s n) (af n).1=0.
    rewrite he /smooth_test_value linear0; exact:(smooth_function_zero_value hE _).
  apply:hy; by rewrite -(hAf n).2.2.1 hv.
exists s; split; first exact hNe; split.
- move=>A hA hZero.
  have [[i L] [r [hr hBall]]]:=((smooth_function_topology_laws hD).2 A).1 hA (inc 0) hZero.
  have [N [W [hW [hLW hWN]]]]:=smooth_compact_exhaustion_neighbourhood hK L.
  exists N; first exact Logic.I.
  move=>n hn; apply:hBall.
  rewrite linear0 subr0.
  have hSem:=@smooth_function_derivative_seminorm_laws R X Y NX NY hNX hNY U E ev D hD L i.
  have hz:=@smooth_seminorm_disjoint_support_zero R X Y NX NY hNX hNY U hU E ev D hD L i
    (smooth_function_derivative_seminorm hD L i) hSem (inc (s n)).
  have he:smooth_function_derivative_seminorm hD L i (inc (s n))=0.
    apply:hz=>x hx hs.
    exact:((hAf n).2.2.2 x hs).2
      (smooth_compact_exhaustion_monotone hK hn (hWN x (hLW x hx))).
  by rewrite he.
- move=>L; have [N [W [hW [hLW hWN]]]]:=smooth_compact_exhaustion_neighbourhood hK L.
  exists N=>n hn f he.
  have hValNonzero:ev (inc (s n)) (af n).1<>0.
    change (value (s n) (af n).1<>0); by rewrite (hAf n).2.2.1.
  have hs:@smooth_function_support R X Y NX hNX U E ev (inc (s n)) (af n).1.
    split; first exact:(hAf n).1.
    exact:(@subset_closure (real_norm_metric_space hNX) _ _ hValNonzero).
  rewrite -he smooth_test_step_evaluation in hs.
  have hMem:=subspace_representation_member (smooth_fixed_test_space_laws hE L) f.
  have hLa:=hMem (af n).1 hs.
  apply:(hAf n).2.1.
  exact:(smooth_compact_exhaustion_monotone hK hn (hWN _ (hLW _ hLa))).
Qed.
End EscapingSequence.
