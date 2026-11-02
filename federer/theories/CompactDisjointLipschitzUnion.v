(** Federer (1969), 3.1.16, p. 228: supporting the choice of compact
    Lipschitz pieces and the successive extensions. Disjoint compact
    pieces with Lipschitz restrictions have a Lipschitz union. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import LipschitzUP LipschitzBasic MetricClosedBalls
  CompactNormDomainRadius CompactMetricBounded CompactSetDistanceProfile MetricDiameterUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_disjoint_metric_separation]: supporting compact
    separation for the union of Lipschitz restrictions in Federer 3.1.16,
    p. 228. A compact set and a disjoint closed set have positive distance;
    the statement includes the empty set. *)
Lemma compact_disjoint_metric_separation (R : realType) (X : metricType R)
    (K H : set X) : compact K -> closed H ->
  (forall x, K x -> H x -> False) ->
  exists d : R, 0<d /\ forall x y, K x -> H y -> d<=mdist x y.
Proof.
move=>hK hH hdis.
have hlocal c : K c -> exists r : R, 0<r /\ forall y, mdist c y<r -> ~H y.
  move=>hc; have hO := closed_openC hH.
  have hnc : (~`H) c by move=>hh; exact (hdis c hc hh).
  rewrite openE in hO.
  have [r hr hb] := (metricType_numDomainType.nbhs_mdistP c (~`H)).1 (hO c hnc).
  exists r; split=>// y hy; exact: hb y hy.
have [d [hd hb]] := metric_compact_uniform_domain_radius hK hlocal.
exists d; split=>// x y hx hy.
rewrite leNgt; apply/negP=>hlt; exact (hb x y hx hlt hy).
Qed.

(** Source for [compact_disjoint_lipschitz_union]: supporting the compact
    choices and repeated use of 2.10.43 in Federer 3.1.16, p. 228.
    The positive separation bounds cross-piece quotients; within each
    piece its original bound applies. No finiteness of ambient dimension
    or prior boundedness of the function is required. *)
Theorem compact_disjoint_lipschitz_union (R : realType) (X Y : metricType R)
    (K H : set X) (f : X->Y) :
  compact K -> compact H -> (forall x, K x -> H x -> False) ->
  is_metric_lipschitz K f -> is_metric_lipschitz H f ->
  is_metric_lipschitz (K `|` H) f.
Proof.
move=>hK hH hdis [L [hL [hL0 hLf]]] [M [hM [hM0 hMf]]].
case: (pselect (exists a, K a))=>[[a ha]|hKe]; last first.
  exists M; split=>//; split=>// x y hx hy.
  have hh z : K z \/ H z -> H z by case=>// hk; exfalso; apply: hKe; exists z.
  exact (hMf x y (hh x hx) (hh y hy)).
case: (pselect (exists b, H b))=>[[b hb]|hHe]; last first.
  exists L; split=>//; split=>// x y hx hy.
  have hh z : K z \/ H z -> K z by case=>// hh; exfalso; apply: hHe; exists z.
  exact (hLf x y (hh x hx) (hh y hy)).
have hnK : K !=set0 by exists a.
have hnH : H !=set0 by exists b.
pose CK : compact_metric_set X := exist _ K (mem_set (conj hK hnK)).
pose CH : compact_metric_set X := exist _ H (mem_set (conj hH hnH)).
have [r [hr hKr]] := compact_metric_set_ball_bound CK a.
have [s [hs hHs]] := compact_metric_set_ball_bound CH b.
have [d [hd hsep]] := compact_disjoint_metric_separation hK (compact_closed (@metric_hausdorff R X) hH) hdis.
pose B := L*r+mdist (f a) (f b)+M*s.
have hB : 0<=B := addr_ge0 (addr_ge0 (mulr_ge0 hL0 (ltW hr)) (mdist_ge0 _ _)) (mulr_ge0 hM0 (ltW hs)).
have hq : 0<=B/d := divr_ge0 hB (ltW hd).
pose C := L+M+B/d.
have hC0 : 0<=C := addr_ge0 (addr_ge0 hL0 hM0) hq.
have hLC : L<=C by rewrite /C; lra.
have hMC : M<=C by rewrite /C; lra.
have hcross x y : K x -> H y -> mdist (f x) (f y)<=C*mdist x y.
  move=>hx hy.
  have hxa : mdist x a<=r by rewrite metric_sym; exact (hKr x hx).
  have hby : mdist b y<=s := hHs y hy.
  have hbnd : mdist (f x) (f y)<=B.
    apply: le_trans (metric_triangle (f x) (f a) (f y)) _.
    have hyb := metric_triangle (f a) (f b) (f y).
    have hx1 := le_trans (hLf x a hx ha) (ler_wpM2l hL0 hxa).
    have hy1 := le_trans (hMf b y hb hy) (ler_wpM2l hM0 hby).
    rewrite /B; lra.
  have hxy := hsep x y hx hy.
  have hBd : B<=(B/d)*mdist x y.
    have hh := ler_wpM2l hq hxy.
    by rewrite divfK ?gt_eqF in hh.
  apply: le_trans hbnd (le_trans hBd _).
  apply: ler_wpM2r; first exact: mdist_ge0.
  rewrite /C; have := hL0; have := hM0; lra.
apply: (@metric_lipschitz_of_bound R X Y (K `|` H) f C); split=>// x y [hx|hx] [hy|hy].
- exact (le_trans (hLf x y hx hy) (ler_wpM2r (mdist_ge0 x y) hLC)).
- exact (hcross x y hx hy).
- rewrite (metric_sym (f x) (f y)) (metric_sym x y); exact (hcross y x hy hx).
- exact (le_trans (hMf x y hx hy) (ler_wpM2r (mdist_ge0 x y) hMC)).
Qed.
