(** Federer (1969), 4.1.26, pp. 383–384:
    almost constancy of a total representative
    gives almost constancy of the original
    partial degree. The original conull domain
    is retained, rather than replacing it by
    an everywhere-defined degree. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionExtensionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_density_almost_constant_from_extension]:
    the relative almost-constancy convention in
    4.1.26, pp. 383–384, applied to
    the original partial signed-density graph. *)
Theorem partial_density_almost_constant_from_extension (R:realType)
    (X:choiceType) (mu:set X->\bar R) (hMu:is_measure mu)
    (d:partial_function X R) (r:X->R) (W:set X) c:
  is_partial_function_total_extension d r->
  measure_almost_everywhere mu (partial_function_domain d)->
  measure_almost_everywhere_on mu W [set x|r x=c]->
  measure_almost_everywhere_on mu W [set x|partial_function_graph d x c].
Proof.
move=>hR hDomain hConstancy.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
have hImp:measure_almost_everywhere mu [set x|W x->r x=c]:=
  (measure_almost_everywhere_on_implication _ _ _).1 hConstancy.
apply:(@measure_almost_everywhere_mono R X mu hMu _ _ _
  (measure_almost_everywhere_and hMu hDomain hImp))=>x [[a ha] hConstant] hx.
have hA:a=c:=eq_trans (esym (hR x a ha)) (hConstant hx).
by rewrite -hA.
Qed.
