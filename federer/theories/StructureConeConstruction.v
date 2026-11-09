(** Private existence for the cone specified in Federer (1969),
    3.3.1, printed p. 287. Use the already sealed distance to a
    nonempty set and prove independence from its realization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces
  ModuleQuotient EuclideanInnerProduct InnerMetric InnerNorm
  MetricSetDistanceSealed MetricSetDistanceBasic StructureConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_exists]: existence of the set in
    Federer 3.3.1, p. 287. A vector subspace contains zero, so the
    sealed real distance exists. Its uniqueness proves the exact
    specification for every other realization of that distance. *)
Theorem structure_cone_exists (R:realType) n k (V:G (R_n R n) k)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R):
  exists C,is_structure_cone V a r s C.
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose A:set E:=[set x|grassmann_val V x].
have hA:A!=set0 by exists 0; exact:subspace_zero.
pose d:=@MetricSetDistance.value R E A hA.
have hd:=@MetricSetDistance.laws R E A hA.
exists [set x:E|s^-1*d (x-a)<inner_norm (@euclidean_inner_productP R n) (x-a) /\
  ((inner_norm (@euclidean_inner_productP R n) (x-a))%:E<r)%E].
move=>e he x.
have hde:=metric_set_distance_unique hd he (x-a).
change ((s^-1*d (x-a)<inner_norm (@euclidean_inner_productP R n) (x-a) /\
  ((inner_norm (@euclidean_inner_productP R n) (x-a))%:E<r)%E) <->
  (s^-1*e (x-a)<inner_norm (@euclidean_inner_productP R n) (x-a) /\
  ((inner_norm (@euclidean_inner_productP R n) (x-a))%:E<r)%E)).
by rewrite /d hde.
Qed.

(** Source for [structure_cone_unique]: uniqueness of the set
    defined in Federer 3.3.1, p. 287, from its membership law.
    No positive-radius or nonzero-dimensional case is discarded. *)
Theorem structure_cone_unique (R:realType) n k (V:G (R_n R n) k)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R) C D:
  is_structure_cone V a r s C ->is_structure_cone V a r s D -> C=D.
Proof.
move=>hC hD.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose A:set E:=[set x|grassmann_val V x].
have hA:A!=set0 by exists 0; exact:subspace_zero.
have hd:=@MetricSetDistance.laws R E A hA.
apply/seteqP; split=>x hx.
- apply/(hD _ hd x); exact/(hC _ hd x).
- apply/(hC _ hd x); exact/(hD _ hd x).
Qed.
