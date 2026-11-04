(** Public actual curve distance, Federer (1969), 3.2.46, p. 281.
    Only the independent order laws are used downstream. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianCurveCost RiemannianDistanceUP RiemannianDistanceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ereal_scope.

(** Source for [riemannian_distance]: rho defined by actual curve
    costs, Federer 3.2.46, p. 281. Extended values retain arbitrary
    disconnected coordinate domains. *)
Definition riemannian_distance (R : realType) n A g x y :=
  @RiemannianDistance.value R n A g x y.

(** Source for [riemannian_distance_laws]: independent infimum
    laws of rho, Federer 3.2.46, p. 281. *)
Lemma riemannian_distance_laws (R : realType) n A g x y :
  @is_riemannian_curve_distance R n A g x y
    (@riemannian_distance R n A g x y).
Proof. exact: RiemannianDistance.laws. Qed.

(** Source for [riemannian_distance_nonnegative]: rho>=0,
    supporting the metric claim in Federer 3.2.46, p. 281. *)
Lemma riemannian_distance_nonnegative (R : realType) n A g x y :
  0 <= @riemannian_distance R n A g x y.
Proof.
apply: (riemannian_distance_greatest (riemannian_distance_laws A g x y)).
move=> C a b _; exact: riemannian_curve_cost_nonnegative.
Qed.

(** Source for [riemannian_distance_no_curve]: the infimum over
    no connecting curves is infinite, by 2.1.1, p. 51, applied to
    the definition in Federer 3.2.46, p. 281. Finite component
    metrics must therefore be localised on a disconnected A. *)
Lemma riemannian_distance_no_curve (R : realType) n A g x y :
  (forall C a b, ~ @is_riemannian_admissible_curve R n A x y C a b) ->
  @riemannian_distance R n A g x y = +oo.
Proof.
move=> h; apply/eqP; rewrite eq_le leey andTb.
apply: (riemannian_distance_greatest (riemannian_distance_laws A g x y)).
by move=> C a b hC; exfalso; exact: h hC.
Qed.
