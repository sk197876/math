(** Federer (1969), 3.2.22(3), p. 258:
    preserve an integrable weight on its exact domain
    and use an auxiliary total zero-off-source representative. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionUP
  PartialFunctionExtensionSealed PartialZeroExtension MeasureUP MeasureRestriction MeasureIntegralUP
  MeasureIntegralGraphEquivalence RestrictedIntegralIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [supported_partial_integrable_weight_extension]:
    supporting the actual-domain weight in Federer
    3.2.22(3), p. 258, using the subset convention
    2.4.10, p. 85. First zero-extend the actual
    graph outside W, then use the existing opaque
    total-extension laws. The resulting auxiliary weight
    agrees with every original value, is zero outside W,
    and is integrable for the ambient measure. Neither
    signed infinite integral is excluded. *)
Theorem supported_partial_integrable_weight_extension (R:realType) (X:choiceType)
    (rho:set X->\bar R) (hr:is_measure rho) (W:set X)
    (g:partial_function X (extended_real_line R)):
  measure_measurable rho W ->partial_function_domain g=W ->
  is_measure_integrable (measure_restrict rho W) g ->
  exists u:X->extended_real_line R,
    is_measure_integrable rho (partial_function_total u) /\
    (forall x,W x ->partial_function_graph g x (u x)) /\
    (forall x,~W x ->u x=0) /\
    (forall x z,partial_function_graph
      (partial_function_zero_extension (0:extended_real_line R) W g) x z <->u x=z).
Proof.
move=>hW hDomain [a hI].
pose cut:=partial_function_zero_extension (0:extended_real_line R) W g.
pose u:=@PartialFunctionExtension.value X (extended_real_line R) cut 0.
have hExt:=@PartialFunctionExtension.laws X (extended_real_line R) cut 0.
have hOn x:W x ->partial_function_graph g x (u x).
  move=>hx; have hDomX:partial_function_domain g x by rewrite hDomain.
  have [z hz]:=hDomX.
  have hCut:partial_function_graph cut x z:=(partial_function_zero_extension_on _ _ _ hx).2 hz.
  have hValue:u x=z:=hExt x z hCut; by rewrite hValue.
have hOff x:~W x ->u x=0.
  move=>hx; exact:(hExt x 0 ((partial_function_zero_extension_off _ _ _ hx).2 (erefl 0))).
have hValue x:partial_function_graph cut x (u x).
  have [hx|hx]:=pselect (W x).
  - exact:(partial_function_zero_extension_on _ _ _ hx).2 (hOn x hx).
  - apply:(partial_function_zero_extension_off _ _ _ hx).2; exact:(hOff x hx).
have hGraph x z:partial_function_graph cut x z <->u x=z.
  split; first exact:(hExt x z).
  move=>hz; by rewrite -hz.
have hGlobal: is_measure_integral rho cut a.
  exact:((@restricted_integral_zero_extension_iff R X rho hr W g a hW).1 hI).
exists u; split.
- exists a; apply:(measure_integral_graph_equivalent _ hGlobal)=>x z; exact:(hGraph x z).
- by split; last split.
Qed.
