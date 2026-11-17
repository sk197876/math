(** Federer (1969), 3.4.8(11), pp. 333–335:
    the original finite analytic variety is closed
    relative to its defining domain. Reuse the
    existing open nonzero-locus theorem for each
    actual equation; no global analytic extension is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP NormAnalyticLocal NormRegularity
  NormClassZeroNonzeroLocus FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_variety_relative_closed_form]:
    the relative closedness used in the original
    small-neighbourhood and closure arguments,
    3.4.8(11), pp. 333–335. The ambient
    closed representative is the complement of the
    union of the actual nonzero equation loci. *)
Theorem finite_analytic_variety_relative_closed_form (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U S:set X):
  @is_finite_analytic_variety R X NX hNX U S ->
  exists C:set X,@closed (real_norm_metric_space hNX) C /\S = U `&` C.
Proof.
move=>[hU [I [f [hAnalytic hEquation]]]].
pose O:set X:=\bigcup_(i:I) [set x|U x /\f i x!=0].
have hOpen:@open (real_norm_metric_space hNX) O.
  apply:bigcup_open=>i _.
  exact:(@norm_class_zero_nonzero_locus_open R X R^o NX (fun z:R^o=>`|z|)
    hNX (@scalar_absolute_value_norm R) U (f i)
    (norm_class_continuous (norm_analytic_class_all_orders (hAnalytic i) 0%N))).
exists (~` O);split;first exact:open_closedC hOpen.
apply/seteqP;split.
- move=>x /hEquation [hx hZero];split;first exact:hx.
  move=>[i _ [_ hNonzero]];by rewrite hZero eqxx in hNonzero.
- move=>x [hx hNot];apply/(hEquation x);split;first exact:hx.
  move=>i;apply:contrapT=>hNonzero;apply:hNot;exists i;first exact:Logic.I.
  split;first exact:hx.
  apply/eqP;exact:hNonzero.
Qed.
