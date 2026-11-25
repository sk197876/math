(** Federer (1969), 3.2.25, p. 261: normalization
    S divided by its norm is Borel even at the auxiliary
    zero value. Continuity is used only off zero, where
    the resulting vector has unit norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  BorelFunctionUP BorelFunctionBasic BorelContinuousRegion TopologicalBorel FiniteExceptionalBorel
  RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_unit_normalization]: the pointwise
    expression S divided by its norm in 3.2.25,
    p. 261. Its zero value is auxiliary and never
    asserted to be a unit vector. *)
Definition inner_unit_normalization (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (x:V):V:=
  (inner_norm hB x)^-1*:x.

(** Source for [inner_unit_normalization_norm]: normalization
    produces a unit vector when S is nonzero, as in
    the formula for T in 3.2.25, p. 261. *)
Lemma inner_unit_normalization_norm (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (x:V):
  0<inner_norm hB x ->inner_norm hB (inner_unit_normalization hB x)= 1.
Proof.
move=>hPositive.
have hNonzero:inner_norm hB x!=0 by rewrite (gt_eqF hPositive).
have hUnit:inner_norm hB x \is a GRing.unit by rewrite unitfE hNonzero.
rewrite /inner_unit_normalization inner_normZ (normrV hUnit)
  (ger0_norm (ltW hPositive)); exact:mulVf hNonzero.
Qed.

(** Source for [inner_unit_normalization_borel]: supporting
    measurability of T in 3.2.25, p. 261. The norm
    and reciprocal scaling are continuous off the Borel zero
    locus; the actual zero extension is Borel by 2.2.14,
    p. 70. No value at zero is used in the unit-range law. *)
Theorem inner_unit_normalization_borel (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B):
  is_borel_function (fun x:inner_metric_space hB=>
    (inner_unit_normalization hB x:inner_metric_space hB)).
Proof.
pose M:=inner_metric_space hB.
pose N:=inner_norm hB.
pose D:set M:=[set x|N x!=0].
have hN:continuous (fun x:M=>(N x:real_line_metric R)).
  have hEq:(fun x:M=>(N x:real_line_metric R))=(fun x:M=>(`|x| : real_line_metric R)).
    by apply:funext=>x; rewrite inner_norm_topologyE.
  rewrite hEq; exact:norm_continuous.
have hDBorel:borel_set D.
  have hZero:@borel_set (real_line_metric R) [set 0%R].
    exact:(@finite_metric_set_borel R [the metricType R of real_line_metric R] [set 0%R]
      (@finite_set1 [the choiceType of real_line_metric R] (0:R))).
  have hRaw:=borel_function_preimage (continuous_borel_function hN) (borel_set_complement hZero).
  have hEq:D=(fun x:M=>(N x:real_line_metric R)) @^-1` (~` [set 0%R]).
    apply/seteqP; split=>x; first by move=>/eqP hx.
    by move=>hx; apply/eqP.
  by rewrite hEq.
have hContinuous x:D x ->{for x,continuous (fun y:M=>(inner_unit_normalization hB y:M))}.
  move=>hx; apply:continuousZ; last by move=>U hU; exact hU.
  exact:(continuousV hx (hN x)).
have hPatch:=@borel_continuous_region_extension M M D
  (fun x:M=>(inner_unit_normalization hB x:M)) (0:M) hDBorel hContinuous.
have hEq:(fun x:M=>if pselect (D x) then (inner_unit_normalization hB x:M) else 0)=
    (fun x:M=>(inner_unit_normalization hB x:M)).
  apply:funext=>x; case:pselect=>hx; first by [].
  have hZero:N x=0.
    have [hEqual|hNonzero]:=eqVneq (N x) 0; first exact hEqual.
    exfalso; exact:hx hNonzero.
  by rewrite /inner_unit_normalization -/N hZero invr0 scale0r.
by rewrite hEq in hPatch.
Qed.
