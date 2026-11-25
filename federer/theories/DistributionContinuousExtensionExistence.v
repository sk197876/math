(** Federer (1969), 4.1.5, pp. 349–350: the
    actual finite-gauge limit defines one linear extension
    to compact continuous vector fields. The uniform-limit
    specification precedes this existence construction.
    Choices occur only in this proof of existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP FunctionLatticeUP CompactSupportFunctionUP VectorDaniellHypotheses
  CompactContinuousVectorFields CompactContinuousDomainFields CompactUniformApproximationUP
  CompactUniformApproximationAlgebra DistributionVariationUP DistributionCompactUniformLimits
  DistributionCompactUniformUniqueness DistributionContinuousExtensionUP PositiveNormLimitUP PositiveRealLinearLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionContinuousExtensionExistence.
Variable R:realType.
Variable X:topologicalType.
Variable U:set X.
Hypothesis hh:hausdorff_space X.
Hypothesis hl:locally_compact (@setT X).
Hypothesis hU:open U.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.
Local Notation Q := (@compact_continuous_domain_fields R X U Y NY hNY).
Local Notation A := (@is_compact_uniform_test_approximation R X U Y NY E value).
Local Notation PLimit := (@positive_norm_limit R R^o (fun a:R^o=>`|a|)).
Hypothesis hFinite:forall f:X->R,
  @positive_function_lattice R X (@compactly_supported_continuous_functions R X) f ->
  @real_function_support R X f `<=` U ->
  exists b:R,is_distribution_variation_value NY value S f b%:E.
Hypothesis hValues:forall phi:E,Q (value phi).
Hypothesis hApprox:forall w:X->Y,Q w ->exists P:R->E,A w P.

(** Source for [distribution_continuous_extension_exists]:
    existence, linearity and agreement of the original
    T on D in Federer 4.1.5, pp. 349–350. The
    approximation premises are discharged by the actual
    compact continuous convolution theorem in the original
    Euclidean application. *)
Theorem distribution_continuous_extension_exists:
  exists T:(X->Y)->R,is_distribution_continuous_extension U hNY value S T.
Proof.
have hEach w:exists t:R,Q w ->forall P:R->E,A w P ->PLimit (fun e=>S (P e)) t.
  case:(pselect (Q w))=>hW.
  - have[P hP]:=@hApprox w hW.
    have[t ht]:=@distribution_compact_uniform_limit_exists R X U hh hl hU Y NY hNY E value S hFinite w P hP.
    exists t=>_ P' hP'.
    have[u hu]:=@distribution_compact_uniform_limit_exists R X U hh hl hU Y NY hNY E value S hFinite w P' hP'.
    have hEq:=@distribution_compact_uniform_limit_unique R X U Y NY hNY E value S hh hl hU hFinite
      w P P' t u hP hP' ht hu.
    by rewrite hEq.
  - exists 0=>h; exfalso; exact:hW h.
have[T hT]:=choice hEach.
have hQ:=@compact_continuous_domain_vector_space R X U Y NY hNY.
exists T; constructor.
- move=>w v hw hv.
  have[P hP]:=@hApprox w hw; have[P' hP']:=@hApprox v hv.
  have hSumQ:Q (fun x=>w x+v x):=@vector_function_space_add R X Y Q hQ w v hw hv.
  have hSumA:=@compact_uniform_test_approximation_add R X U Y NY hNY E value w v P P' hP hP'.
  have hLeft:=hT (fun x=>w x+v x) hSumQ (fun e=>P e+P' e) hSumA.
  have hRight:=@positive_real_limit_add R (fun e=>S (P e)) (fun e=>S (P' e)) (T w) (T v)
    (hT w hw P hP) (hT v hv P' hP').
  have hEvaluation:(fun e=>S (P e+P' e))=(fun e=>S (P e)+S (P' e)).
    apply:funext=>e; exact:linearD.
  rewrite hEvaluation in hLeft.
  exact:(@positive_norm_limit_unique R R^o (fun a:R^o=>`|a|) (@scalar_absolute_value_norm R)
    _ _ _ hLeft hRight).
- move=>c w hw.
  have[P hP]:=@hApprox w hw.
  have hScaleQ:Q (fun x=>c*:w x):=@vector_function_space_scale R X Y Q hQ c w hw.
  have hScaleA:=@compact_uniform_test_approximation_scale R X U Y NY hNY E value w P c hP.
  have hLeft:=hT (fun x=>c*:w x) hScaleQ (fun e=>c*:P e) hScaleA.
  have hRight:=@positive_real_limit_scale R (fun e=>S (P e)) (T w) c (hT w hw P hP).
  have hEvaluation:(fun e=>S (c*:P e))=(fun e=>c*S (P e)).
    apply:funext=>e; by rewrite linearZ.
  rewrite hEvaluation in hLeft.
  exact:(@positive_norm_limit_unique R R^o (fun a:R^o=>`|a|) (@scalar_absolute_value_norm R)
    _ _ _ hLeft hRight).
- move=>phi.
  have hPhi:=hValues phi.
  have hConstant:A (value phi) (fun _:R=>phi).
    exists (@real_function_support R X (fun x=>NY (value phi x))); split; first exact:hPhi.1.2.
    split; first exact:hPhi.2.
    exists 1; split; first exact:ltr01.
    split.
    + move=>e _ _ x hx; exact:(@compact_continuous_vector_zero_off_norm_support R X Y NY hNY _ x hx).
    + move=>eta hEta; exists 1; split; first exact:ltr01.
      by move=>e _ _ x; rewrite subrr (real_seminorm_zero hNY.1).
  have hLeft:=hT (value phi) hPhi (fun _:R=>phi) hConstant.
  exact:(@positive_norm_limit_unique R R^o (fun a:R^o=>`|a|) (@scalar_absolute_value_norm R)
    (fun _:R=>S phi) _ (S phi) hLeft
    (@positive_norm_limit_constant R R^o (fun a:R^o=>`|a|) (@scalar_absolute_value_norm R) (S phi))).
- exact:hT.
Qed.
End DistributionContinuousExtensionExistence.
