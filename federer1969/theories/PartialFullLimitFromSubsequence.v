(** Federer (1969), 4.1.18, p. 376: the
    almost-everywhere sum of the coefficient series agrees
    with its L1 limit. Reuse metric uniqueness and
    the original subsequence convention of 2.3.10,
    p. 80; partial target domains remain unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureConvergenceSubsequenceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_full_limit_from_subsequence]:
    agreement of the pointwise and L1 coefficient
    sums in Federer 4.1.18, p. 376, by
    uniqueness of a metric limit along the original
    strict subsequence of 2.3.10, p. 80. *)
Theorem partial_full_limit_from_subsequence (R:realType) (X:choiceType)
    (Y:metricType R) (mu:set X->\bar R) (hm:is_measure mu)
    (f:nat->X->Y) (g:partial_function X Y) (s:nat->nat):
  (forall i,(s i<s i.+1)%N)->
  measure_almost_everywhere mu [set x | exists y:Y,(fun i=>f i x) @ \oo --> y]->
  measure_almost_everywhere mu (partial_function_limit_locus
    (fun i=>partial_function_total (f (s i))) g)->
  measure_almost_everywhere mu (partial_function_limit_locus
    (fun i=>partial_function_total (f i)) g).
Proof.
move=>hStrict hFull hSubsequence.
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _
  (measure_almost_everywhere_and hm hFull hSubsequence))
  =>x [[z hZ] [u [y [hU [hY hLimit]]]]].
have hValues:u=(fun i=>f (s i) x).
  apply:funext=>i;exact:(esym (hU i)).
have hZSubsequence:=@strict_subsequence_topological_limit Y
  (fun i=>f i x) z s hStrict hZ.
have hULimit:u @ \oo --> z by rewrite hValues;exact:hZSubsequence.
have PF0:ProperFilter (\oo:set_system nat) by typeclasses eauto.
have PF:ProperFilter (u @ \oo):=@fmap_proper_filter nat Y u \oo PF0.
have hSame:y=z:=@cvg_unique Y (@metric_hausdorff R Y) (u @ \oo) PF
  y z hLimit hULimit.
exists (fun i=>f i x),y;split;first by move=>i.
split;first exact:hY.
by rewrite hSame.
Qed.
