(** Federer (1969), 3.2.35, p. 271:
    the original open convex boundary is the
    unit level of the actual Minkowski gauge. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealNormUP NormMetric InnerConvex MinkowskiGaugeUP
  NormOpenConvexMinkowskiSublevel NormOpenConvexMinkowskiClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_open_convex_minkowski_boundary]:
    the boundary level underlying the radial
    representation in Federer 3.2.35, p. 271.
    Boundary means closure minus interior in the
    original norm topology. The proved strict and
    closed gauge sublevels give exactly g=1;
    no boundary identity is assumed. *)
Theorem norm_open_convex_minkowski_boundary (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) (g:V->R):
  @is_minkowski_gauge R V S g ->
  @open [the topologicalType of real_norm_metric_space hN] S ->
  is_inner_convex S ->S 0 ->forall x:V,
  (@closure [the topologicalType of real_norm_metric_space hN] S x /\
    ~@interior [the topologicalType of real_norm_metric_space hN] S x) <->g x= 1.
Proof.
move=>hG hOpen hConvex hZero x.
have hSublevel:=@norm_open_convex_minkowski_sublevel R V N hN S g hG hOpen hConvex hZero x.
have hClosure:=@norm_open_convex_minkowski_closure R V N hN S g hG hOpen hConvex hZero x.
split.
- move=>[hx hOutside].
  have hUpper:g x<=1:=hClosure.1 hx.
  have hNoStrict:~g x<1.
    move=>hStrict; apply:hOutside.
    exact:(open_nbhs_nbhs (conj hOpen (hSublevel.2 hStrict))).
  apply/eqP; rewrite eq_le hUpper /=.
  rewrite leNgt; apply/negP; exact hNoStrict.
- move=>he; split.
  + apply:hClosure.2; by rewrite he.
  + move=>hInterior.
    have hMember:S x:=interior_subset hInterior.
    have hStrict:=hSublevel.1 hMember.
    by rewrite he ltxx in hStrict.
Qed.
