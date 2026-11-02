(** Federer (1969), 2.2.7, p. 64: existence of the least Lipschitz constant.
    This private construction uses real completeness only; the metric
    inequality at the infimum is proved here. Public users will use the
    sealed least-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [least_metric_lipschitz_constant_exists]: Federer 2.2.7, p.
    64, first paragraph, direct existence assertion. The infimum of the
    nonnegative admissible bounds is itself admissible: each
    nonzero-distance ratio is a lower bound of that set. Zero-distance pairs
    use the metric separation law. *)
Theorem least_metric_lipschitz_constant_exists (R : realType)
    (T U : metricType R) (X : set T) (f : T -> U) :
  is_metric_lipschitz X f -> exists L, is_least_metric_lipschitz_constant X f L.
Proof.
move=> [M [hM hf]].
pose S := [set L | is_metric_lipschitz_bound X f L].
have hn : S !=set0 by exists M.
have hl : lbound S 0 by move=> L [hL _].
have hb : has_lbound S by exists 0.
exists (inf S); constructor.
- split; first exact: lb_le_inf hn hl.
  move=> x y hx hy; case: (eqVneq x y)=> [->|hxy].
  + by rewrite !mdistxx mulr0.
  + have hd : 0 < mdist x y by rewrite mdist_gt0.
    rewrite -(ler_pdivrMr _ _ hd).
    apply: lb_le_inf hn _=> L [hL hLf].
    rewrite (ler_pdivrMr _ _ hd); exact: hLf x y hx hy.
- move=> L hL; exact: (ge_inf hb hL).
Qed.
