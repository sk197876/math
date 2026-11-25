(** Proved existence and uniqueness for the independent cone-density
    upper-limit specification of Federer (1969), 3.3.2,
    pp. 287–288. Existing sealed order bounds supply witnesses;
    no Borel measurability theorem is assumed in the construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  ExtendedRealBoundsUP ExtendedRealBounds StructureConeDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_density_exists]: existence of
    the upper limit in Federer 3.3.2, pp. 287–288,
    by the independent extended order-bound laws of 2.1.1,
    p. 51. No regularity or finiteness premise is needed
    merely to define the original extended-valued expression. *)
Theorem structure_cone_density_exists (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R):
  exists f,is_structure_cone_density hmn phi A delta f.
Proof.
pose g z t:=extended_real_sup [set v|exists r s:R,
  (0<r<delta) /\ (0<s<t) /\ v=structure_cone_cost hmn phi A z r s].
have hg z t:is_structure_cone_tail_supremum hmn phi A delta z t (g z t).
  constructor; [exact:extended_real_sup_upper|exact:extended_real_sup_least].
exists (fun z=>extended_real_inf [set q|exists t:R,0<t /\ q=g z t])=>z; split.
- move=>t q ht hq.
  have he:q=g z t:=extended_real_supremum_unique hq (hg z t).
  rewrite he; apply:extended_real_inf_lower; by exists t.
- move=>b hBound; apply:extended_real_inf_greatest=>q [t [ht ->]].
  exact:(hBound t (g z t) ht (hg z t)).
Qed.

(** Source for [structure_cone_density_unique]: uniqueness
    of the actual upper limit in Federer 3.3.2,
    pp. 287–288, from the independent greatest-lower-bound
    laws, without referring to the witness construction. *)
Theorem structure_cone_density_unique (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R) f g:
  is_structure_cone_density hmn phi A delta f ->
  is_structure_cone_density hmn phi A delta g ->f=g.
Proof.
move=>hf hg; apply:funext=>z; apply/eqP; rewrite eq_le; apply/andP; split.
- exact:((hg z).2 (f z) (hf z).1).
- exact:((hf z).2 (g z) (hg z).1).
Qed.
