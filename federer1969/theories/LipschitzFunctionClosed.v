(** Federer (1969), 2.10.21, p. 182: the set E_s of functions with Lipschitz
    bound s is closed in the cartesian product topology. The proof uses the
    printed intersection of the two-point closed distance constraints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import LipschitzUP MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_metric_distance_constraint_closed]: supporting
    closed two-point constraint in 2.10.21, p. 182.
    Two continuous maps into a metric space have a
    closed set on which their mutual distance is at most t. *)
Lemma continuous_metric_distance_constraint_closed (R : realType) (P : topologicalType)
    (Y : metricType R) (f g : P -> Y) (t : R) :
  continuous f -> continuous g -> closed [set p | mdist (f p) (g p)<=t].
Proof.
move=> hf hg; have ho : open (~` [set p | mdist (f p) (g p)<=t]).
  rewrite openE=> p hp.
  have htp : t<mdist (f p) (g p) by rewrite ltNge; apply/negP.
  pose e := (mdist (f p) (g p)-t)/3.
  have he : 0<e by rewrite /e divr_gt0 // subr_gt0.
  have hfn : nbhs p (f @^-1` ball (f p) e) := hf p _ (nbhsx_ballx (f p) e he).
  have hgn : nbhs p (g @^-1` ball (g p) e) := hg p _ (nbhsx_ballx (g p) e he).
  apply: (@filterS P (nbhs p) _ _ _ _ (filterI hfn hgn))=> q [hqf hqg] hq.
  rewrite !ballEmdist /= in hqf hqg.
  have h1 := metric_triangle (f p) (f q) (g p).
  have h2 := metric_triangle (f q) (g q) (g p).
  rewrite (metric_sym (g q) (g p)) in h2.
  rewrite /e in hqf hqg; change (is_true (mdist (f q) (g q)<=t)) in hq; lra.
have hc := open_closedC ho; by rewrite setCK in hc.
Qed.

(** Source for [metric_lipschitz_functions]: direct E_s
    of 2.10.21, p. 182, as a subset of the
    cartesian product. Nonnegative constants include zero. *)
Definition metric_lipschitz_functions (R : realType) (X Y : metricType R) (s : R) :
    set (prod_topology (fun _ : X => Y)) :=
  [set f | is_metric_lipschitz_bound setT f s].

(** Source for [metric_lipschitz_functions_closed]: direct
    first assertion of 2.10.21, p. 182: E_s
    is the intersection of its closed pair constraints. *)
Theorem metric_lipschitz_functions_closed (R : realType) (X Y : metricType R) (s : R) :
  0<=s -> closed (@metric_lipschitz_functions R X Y s).
Proof.
move=> hs.
have he : @metric_lipschitz_functions R X Y s=
    \bigcap_(xy in [set: (X*X)%type]) [set f : prod_topology (fun _ : X => Y) |
      mdist (f xy.1) (f xy.2)<=s*mdist xy.1 xy.2].
  apply/seteqP; split.
  - by move=> f [h0 hf] [x y] _; exact: hf x y I I.
  - move=> f hf; split=> // x y _ _; exact: hf (x,y) I.
rewrite he; apply: closed_bigI=> xy hxy.
apply: continuous_metric_distance_constraint_closed; exact: proj_continuous.
Qed.
