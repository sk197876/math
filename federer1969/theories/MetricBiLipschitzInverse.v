(** Federer (1969), 3.2.17, p. 254:
    recover the actual restricted inverse from
    the abstract two-sided distance laws. A total
    representative is auxiliary and preserves the
    exact inverse graph on the image. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import LipschitzUP MetricBiLipschitzUP PartialFunctionUP
  PartialFunctionExtensionUP PartialFunctionExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_bilipschitz_injective_on]:
    univalence of the restricted map in
    Federer 3.2.17, p. 254, derived
    from the asserted inverse Lipschitz inequality. *)
Lemma metric_bilipschitz_injective_on (R : realType) (X Y : metricType R)
    (K : set X) (f : X -> Y) (L : R) :
  is_metric_bilipschitz_bound K f L ->
  forall x y, K x -> K y -> f x=f y -> x=y.
Proof.
move=> [_ hb] x y hx hy he.
have hh := hb x y hx hy; rewrite he mdistxx mulr0 in hh.
apply: mdist_positivity; apply/eqP.
rewrite eq_le hh (mdist_ge0 x y); reflexivity.
Qed.

(** Source for [metric_bilipschitz_inverse_exists]:
    the inverse of psi restricted to K,
    Federer 3.2.17, p. 254. The
    total representative is used only on f(K);
    its existence needs an inhabited source, here
    supplied by the book's a in K. *)
Theorem metric_bilipschitz_inverse_exists (R : realType) (X Y : metricType R)
    (K : set X) (f : X -> Y) (L : R) (x0 : X) :
  is_metric_bilipschitz_bound K f L ->
  exists g : Y -> X, (forall x, K x -> g (f x)=x) /\
    is_metric_lipschitz_bound (f @` K) g L.
Proof.
move=> hB.
have hsingle y x z : (K x /\ f x=y) -> (K z /\ f z=y) -> x=z.
  move=> [hx he] [hz he']; apply: (metric_bilipschitz_injective_on hB hx hz).
  exact: eq_trans he (esym he').
pose inv := @Build_partial_function Y X (fun y x=>K x /\ f x=y) hsingle.
pose g := @PartialFunctionExtension.value Y X inv x0.
have hExt := @PartialFunctionExtension.laws Y X inv x0.
have hg x (hx : K x) : g (f x)=x.
  apply: hExt; by split.
exists g; split=> //; split; first exact hB.1.1.
move=> y z [x hx <-] [t ht <-].
rewrite (hg x hx) (hg t ht); exact: hB.2 x t hx ht.
Qed.
