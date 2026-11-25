(** Federer (1969), 3.4.8(11), p. 333:
    a nonempty variety germ contains its
    centre in every original finite-equation
    representative on a neighbourhood. This supporting
    fact follows from continuity of its
    actual defining equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP NormAnalyticLocal NormRegularity
  NormClassZeroTopology NormClassZeroNonzeroLocus FiniteAnalyticVarietyUP AnalyticVarietyGermUP
  SetGermUP SetGermSealed SetGermExistence SetGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_variety_representative_centre]:
    the zero-dimensional variety germ is
    the point germ once its nearby
    common zeros are isolated, 3.4.8(11),
    p. 333. Nonemptiness ensures the
    original centre is a common zero. *)
Theorem analytic_variety_representative_centre (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U S:set X) a:
  U a ->@is_finite_analytic_variety R X NX hNX U S ->
  @set_germ (Topological.clone (real_norm_metric_space hNX) _) a S <>
    @set_germ (Topological.clone (real_norm_metric_space hNX) _) a set0 ->S a.
Proof.
move=>hUa [hU [I [f [hAnalytic hEquation]]]] hNonempty.
apply:(hEquation a).2;split;first exact:hUa.
move=>i;apply:contrapT=>hNonzero;apply:hNonempty.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have hClassZero:=norm_class_continuous (norm_analytic_class_all_orders (hAnalytic i) 0%N).
have hOpen:@open T [set x|U x /\ f i x!=0].
  exact:(@norm_class_zero_nonzero_locus_open R X R^o NX (fun z:R^o=>`|z|) hNX
    (@scalar_absolute_value_norm R) U (f i) hClassZero).
apply/set_germ_equality_original.
exists [set x|U x /\ f i x!=0];split;first exact:hOpen.
split.
- split;first exact:hUa.
  apply/eqP;exact:hNonzero.
apply/seteqP;split.
- move=>x [hS [hx /eqP hNot]];exfalso;apply:hNot;exact:((hEquation x).1 hS).2 i.
- by move=>x [hEmpty _].
Qed.
