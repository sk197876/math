(** Private existence proof for the independently specified curve
    infimum, Federer (1969), 3.2.46, printed p. 281. This construction
    is imported only by the seal and the assumptions audit. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianCurveCost RiemannianDistanceUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_curve_distance_exists]: existence of
    the infimum in Federer 3.2.46, p. 281, by the general complete
    extended-real order of 2.1.1, p. 51. This proves the independent
    laws, without assuming any geometric comparison theorem. *)
Theorem riemannian_curve_distance_exists (R : realType) n A g x y :
  exists d, @is_riemannian_curve_distance R n A g x y d.
Proof.
pose S := [set z | exists C a b,
  is_riemannian_admissible_curve A x y C a b /\
    z = riemannian_curve_cost g C a b].
exists (extended_real_inf S); constructor.
- move=> C a b hC; apply: extended_real_inf_lower.
  by exists C,a,b; split.
- move=> c hc; apply: extended_real_inf_greatest=> z [C [a [b [hC ->]]]].
  exact: hc hC.
Qed.
