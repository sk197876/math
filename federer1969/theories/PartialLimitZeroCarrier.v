(** Federer (1969), 4.1.18, p. 376: the
    L1 field limit can retain the common compact
    carrier. This supporting fact uses only the
    earlier almost-everywhere convergence convention
    of 2.3.2(6), pp. 73–74. No measurability
    or nonemptiness of the carrier is needed here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitUP PartialZeroExtension MeasureUP MeasureAlmostUP
  MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_almost_limit_zero_carrier]:
    the limit of fields vanishing outside a common
    carrier vanishes there almost everywhere, supporting
    the compact sum field in Federer 4.1.18, p. 376.
    Zero extension changes no original almost-everywhere
    value or L1 class. *)
Theorem partial_almost_limit_zero_carrier (R:realType) (X:choiceType)
    (Y:metricType R) (zero:Y) (mu:set X->\bar R) (hm:is_measure mu)
    (K:set X) (f:nat->X->Y) (g:partial_function X Y):
  (forall i x,~K x->f i x=zero)->
  measure_almost_everywhere mu
    (partial_function_limit_locus (fun i=>partial_function_total (f i)) g)->
  measure_almost_equal mu g (partial_function_zero_extension zero K g).
Proof.
move=>hOff hLimit.
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hLimit)
  =>x [u [z [hU [hZ hConverges]]]].
exists z;split;first exact:hZ.
apply/partial_function_zero_extension_graph.
case:(pselect (K x))=>hK.
- left;by split.
- right;split;first exact:hK.
  have hConstant:u=(fun _:nat=>zero).
    apply:funext=>i.
    have hValue:f i x=u i:=hU i.
    rewrite -hValue;exact:hOff i x hK.
  have hZero:u @ \oo --> zero by rewrite hConstant;exact:cvg_cst.
  have PF0:ProperFilter (\oo:set_system nat) by typeclasses eauto.
  have PF:ProperFilter (u @ \oo):=@fmap_proper_filter nat Y u \oo PF0.
  exact:(@cvg_unique Y (@metric_hausdorff R Y) (u @ \oo) PF
    z zero hConverges hZero).
Qed.
