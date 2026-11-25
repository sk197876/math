(** Federer (1969), 4.1.2, p. 348: all
    tagged finite kernel-test sums have one common
    compact support. Tags of nonempty cells belong
    to the original compact; empty cells contribute
    their actual zero measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric MeasureUP MeasureBasic
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSubspaces SmoothTestSpaces SmoothTestEvaluation
  TranslatedKernelTestUP FiniteTaggedBorelPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_kernel_test_sum_support]: the common
    compact step containing the original finite approximations
    in Federer 4.1.2, p. 348. The
    original measures of all empty cells are proved zero. *)
Theorem compact_kernel_test_sum_support (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY (fun _=>True) ev)
    (psi:X->R) r (B:X->Hom Y (smooth_test_space hE))
    (mu:set X->\bar R) (hm:is_measure mu)
    (K C:smooth_compact_set hNX (fun _=>True)) (f:X->Y):
  (forall x,r<NX x ->psi x=0) ->
  @is_translated_kernel_tests R X Y NX NY hNX hNY E ev hE psi B ->
  (forall x z,smooth_compact_carrier K z ->NX (x-z)<=r ->smooth_compact_carrier C x) ->
  forall (I:finType) (A:I->set X) (tag:I->X) (mesh:R),
    @is_finite_tagged_borel_partition R (real_norm_metric_space hNX)
      (smooth_compact_carrier K) mesh I A tag ->
    @smooth_function_support R X Y NX hNX (fun _=>True) E ev
      (smooth_test_inclusion hE (\sum_i fine (mu (A i))*:B (tag i) (f (tag i)))) `<=`
      smooth_compact_carrier C.
Proof.
move=>hOff hB hThick I A tag mesh hPart.
pose S:=smooth_fixed_support_subspace hE C.
have hBSupport a y:smooth_compact_carrier K a ->
    S (smooth_test_inclusion hE (B a y)).
  move=>ha; apply:(smooth_function_compact_support_iff hE C _).2=>x hx.
  change (smooth_test_value hE (B a y) x=0); rewrite hB.
  have hLarge:r<NX (x-a).
    rewrite ltNge; apply/negP=>hSmall; apply:hx; exact:(@hThick x a ha hSmall).
  by rewrite (@hOff (x-a) hLarge) scale0r.
change (S (smooth_test_inclusion hE (\sum_i fine (mu (A i))*:B (tag i) (f (tag i))))).
rewrite linear_sum.
apply:(big_ind S).
- exact:subspace_zero S.
- move=>a b ha hb; exact:(@subspace_add R E S a b ha hb).
- move=>i _.
  case:(pselect (A i !=set0))=>hNonempty.
  + rewrite linearZ /=.
    apply:(@subspace_scale R E S (fine (mu (A i))) _).
    apply:hBSupport.
    exact:(@finite_tagged_partition_inside R (real_norm_metric_space hNX)
      (smooth_compact_carrier K) mesh I A tag hPart i (tag i)
      (@finite_tagged_partition_tag R (real_norm_metric_space hNX)
        (smooth_compact_carrier K) mesh I A tag hPart i hNonempty)).
  + have hEmpty:A i=set0.
      apply/seteqP; split; last by move=>x [].
      move=>x hx; exfalso; apply:hNonempty; by exists x.
    rewrite hEmpty (measure_empty hm) fine0 scale0r linear0.
    exact:subspace_zero S.
Qed.
