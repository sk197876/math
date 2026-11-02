(** Federer (1969), 2.10.44, printed p. 202, final paragraph: every scalar
    Lipschitz map from a metric subspace has a global extension with the
    same optimal constant. On a nonempty source the extension is the printed
    infimum envelope; on an empty source a constant zero extension preserves
    the optimal constant zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import RealMetricBackground LipschitzUP LipschitzBasic LipschitzConstant
  McShaneEnvelopeUP McShaneEnvelopeLaws McShaneEnvelope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_44_scalar_formula]: direct scalar extension and
    printed infimum formula in 2.10.44, p. 202, with the nonempty-source
    qualification explicit. The optimal constant is preserved exactly, and
    no completeness or closedness of the original metric source is assumed. *)
Theorem federer_2_10_44_scalar_formula (R : realType) (X : metricType R) S (f : X -> R)
    (hLip : is_metric_lipschitz S (f : X -> real_line_metric R)) :
  S !=set0 -> exists g : X -> R, exists hGlobal : is_metric_lipschitz setT (g : X -> real_line_metric R),
    (forall x, S x -> g x=f x) /\ metric_lipschitz_constant hGlobal=metric_lipschitz_constant hLip /\
    forall x, g x=inf (mcshane_costs_at S f (metric_lipschitz_constant hLip) x).
Proof.
move=> hne.
pose L := metric_lipschitz_constant hLip.
have hleast := metric_lipschitz_constant_specification hLip.
have hSf : is_metric_lipschitz_bound S (f : X -> real_line_metric R) L := least_metric_lipschitz_bound hleast.
pose g := @mcshane_envelope R X S f L hne hSf.
have hg := @mcshane_envelope_specification R X S f L hne hSf.
have hag := @mcshane_envelope_agreement R X S f L g hSf hg.
have hbound := @mcshane_envelope_lipschitz R X S f L g hSf.1 hg.
have hGlobal : is_metric_lipschitz setT (g : X -> real_line_metric R) := metric_lipschitz_of_bound hbound.
have hGleast : is_least_metric_lipschitz_constant setT (g : X -> real_line_metric R) L.
  constructor=> // M [hM hMb].
  have hOrig : is_metric_lipschitz_bound S (f : X -> real_line_metric R) M.
    split=> // x y hx hy; rewrite -(hag x hx) -(hag y hy); exact: hMb x y I I.
  exact (@least_metric_lipschitz_minimal R X [the metricType R of real_line_metric R] S f L hleast M hOrig).
exists g,hGlobal; split=> //; split.
- exact: least_metric_lipschitz_unique (metric_lipschitz_constant_specification hGlobal) hGleast.
- exact (@mcshane_envelope_infimum R X S f L g hne hg).
Qed.

(** Source for [federer_2_10_44_scalar]: direct arbitrary-
    source scalar extension assertion of 2.10.44,
    p. 202, including an empty original source.
    Only the separate infimum formula needs nonemptiness;
    the existence and optimal-constant conclusion does not. *)
Theorem federer_2_10_44_scalar (R : realType) (X : metricType R) S (f : X -> R)
    (hLip : is_metric_lipschitz S (f : X -> real_line_metric R)) :
  exists g : X -> R, exists hGlobal : is_metric_lipschitz setT (g : X -> real_line_metric R),
    (forall x, S x -> g x=f x) /\ metric_lipschitz_constant hGlobal=metric_lipschitz_constant hLip.
Proof.
case: (pselect (S !=set0))=> [hne|hempty].
- have [g [hg [hag [heq _]]]] := @federer_2_10_44_scalar_formula R X S f hLip hne.
  by exists g,hg.
- have hSf0 : is_metric_lipschitz_bound S (f : X -> real_line_metric R) 0.
    split; first exact: lexx.
    move=> x y hx hy; exfalso; apply: hempty; by exists x.
  have hL0 : metric_lipschitz_constant hLip=0.
    apply/eqP; rewrite eq_le (metric_lipschitz_constant_minimal hLip hSf0)
      (metric_lipschitz_constant_nonnegative hLip); by [].
  pose g : X -> R := fun _=>0.
  have hb : is_metric_lipschitz_bound setT (g : X -> real_line_metric R) 0.
    split; first exact: lexx.
    by move=> x y _ _; rewrite mdistxx mul0r.
  have hGlobal : is_metric_lipschitz setT (g : X -> real_line_metric R) := metric_lipschitz_of_bound hb.
  exists g,hGlobal; split.
  - move=> x hx; exfalso; apply: hempty; by exists x.
  - rewrite hL0; apply/eqP; rewrite eq_le (metric_lipschitz_constant_minimal hGlobal hb)
      (metric_lipschitz_constant_nonnegative hGlobal); by [].
Qed.
