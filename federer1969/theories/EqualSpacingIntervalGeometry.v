(** Federer (1969), 2.10.28(4), pp. 192–193: supporting endpoint geometry
    for equal-length intervals at equally spaced locations. Work with the
    radius and spacing laws, not with a family implementation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge CompactIntervalGaugeGeometry
  MetricDiameter MetricDiameterReal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_spacing_child_in_parent]: supporting
    membership in the parent interval in
    2.10.28(4), p. 192. Its last
    right endpoint is the parent's endpoint
    by d=(n-1)t+s. *)
Lemma equal_spacing_child_in_parent (R : realType) (a d s t N i : R) :
  0<s -> s<t -> d=(N-1)*t+s -> 0<=i -> i<=N-1 ->
  (`[a+i*t,a+i*t+s] : set (real_line_metric R)) `<=` `[a,a+d].
Proof.
move=> hs hst hd hi hiN.
have ht : 0<=t by lra.
have hit : 0<=i*t := mulr_ge0 hi ht.
have hbound := ler_wpM2r ht hiN.
move=> x hx; have /andP[hl hr] : a+i*t<=x<=a+i*t+s by move: hx; rewrite /= in_itv.
rewrite /= in_itv /=; apply/andP; split; lra.
Qed.

(** Source for [equal_spacing_children_separated]: supporting
    disjointness of distinct intervals of
    Phi(J,n) in 2.10.28(4), p. 192.
    A one-index gap gives a strict endpoint
    gap because t>s>0. *)
Lemma equal_spacing_children_separated (R : realType) (a s t i j : R) :
  0<s -> s<t -> i+1<=j ->
  (`[a+i*t,a+i*t+s] : set (real_line_metric R)) `&` `[a+j*t,a+j*t+s]=set0.
Proof.
move=> hs hst hij.
have ht : 0<=t by lra.
have hmul := ler_wpM2r ht hij.
have hgap : a+i*t+s<a+j*t by lra.
have hiord : a+i*t<=a+i*t+s by lra.
have hjord : a+j*t<=a+j*t+s by lra.
apply: (@compact_segments_disjoint_endpoints R _ _ _ _ hiord hjord).2; by left.
Qed.

(** Source for [equal_spacing_child_cost]: supporting
    equal child costs h(s) in 2.10.28(4),
    pp. 192–193. The gauge is arbitrary
    here; only a nonnegative length is needed. *)
Lemma equal_spacing_child_cost (R : realType) (h : R -> R) (a s t i : R) :
  0<=s -> concave_interval_cost h (`[a+i*t,a+i*t+s] : set (real_line_metric R))=h s.
Proof.
move=> hs; have hord : a+i*t<=a+i*t+s by lra.
have hlen : (a+i*t+s)-(a+i*t)=s by lra.
by rewrite (concave_interval_cost_segment h hord) hlen.
Qed.

(** Source for [equal_spacing_child_diameter]: supporting
    positive child diameter and shrinking mesh
    for Phi(J,n) in 2.10.28(4), p. 192,
    and the Cantor construction on p. 193. *)
Lemma equal_spacing_child_diameter (R : realType) (a s t i : R) :
  0<=s -> @extended_metric_diameter R [the metricType R of real_line_metric R]
    `[a+i*t,a+i*t+s]=s%:E.
Proof.
move=> hs; have hord : a+i*t<=a+i*t+s by lra.
have hlen : (a+i*t+s)-(a+i*t)=s by lra.
by rewrite (extended_metric_diameter_segment hord) hlen.
Qed.

(** Source for [natural_strict_index_real_gap]: supporting
    conversion of distinct ordered natural
    child indices to the real spacing
    inequality in 2.10.28(4), p. 192. *)
Lemma natural_strict_index_real_gap (R : realType) (i j : nat) :
  (i<j)%N -> (i%:R+1<=j%:R :> R).
Proof. move=> hij; have hh : (i.+1%:R<=j%:R :> R) by rewrite ler_nat. by rewrite -natr1 in hh. Qed.

(** Source for [natural_index_real_upper_bound]: supporting
    last-child bound i<=n-1 in the zero-based
    indexing of 2.10.28(4), p. 192. *)
Lemma natural_index_real_upper_bound (R : realType) (i n : nat) :
  (i<n)%N -> (i%:R<=n%:R-1 :> R).
Proof. move=> hin; have hh := @natural_strict_index_real_gap R i n hin; lra. Qed.

(** Source for [equal_spacing_ordinal_children_disjoint]: supporting
    disjointness of the n ordinal-indexed
    closed intervals in 2.10.28(4), p. 192.
    Both natural index orders are handled;
    their strict spacing gap includes endpoints. *)
Lemma equal_spacing_ordinal_children_disjoint (R : realType) n (a s t : R) (i j : 'I_n) :
  0<s -> s<t -> i!=j ->
  (`[a+i%:R*t,a+i%:R*t+s] : set (real_line_metric R)) `&`
    `[a+j%:R*t,a+j%:R*t+s]=set0.
Proof.
move=> hs hst hne; case: (ltngtP (val i) (val j))=> [hij|hji|heq].
- exact: (@equal_spacing_children_separated R a s t i%:R j%:R hs hst
    (@natural_strict_index_real_gap R (val i) (val j) hij)).
- rewrite setIC; exact: (@equal_spacing_children_separated R a s t j%:R i%:R hs hst
    (@natural_strict_index_real_gap R (val j) (val i) hji)).
- have he : i=j := val_inj heq; by rewrite he eqxx in hne.
Qed.
