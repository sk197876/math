(** The simultaneous Borel hull in Federer (1969), 2.9.2, p. 153: an
    arbitrary subset of a bounded Borel set has a Borel superset inside that
    set, with the same phi and psi values. Intersect the two regular Borel
    hulls with the parent set. The equality construction itself does not
    require finiteness; the subsequent use of 2.1.4 does. Source context:
    MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [common_borel_hull_inside]: supporting common Borel superset
    in Federer 2.9.2, p. 153 The two equalities follow by monotonicity
    between the original set and each of its Borel hulls. *)
Theorem common_borel_hull_inside (R : realType) (X : topologicalType)
    (phi psi : set X -> \bar R) (A S : set X) :
  is_measure phi -> is_measure psi -> is_borel_regular_measure phi -> is_borel_regular_measure psi ->
  borel_set A -> S `<=` A -> exists T,
    borel_set T /\ S `<=` T /\ T `<=` A /\ phi S=phi T /\ psi S=psi T.
Proof.
move=> hphi hpsi hrphi hrpsi hA hSA.
have [U [hSU [hU heU]]] := borel_regular_cover hrphi S.
have [W [hSW [hW heW]]] := borel_regular_cover hrpsi S.
pose T := U `&` W `&` A.
have hST : S `<=` T by move=> x hx; split; [split; [exact: hSU x hx|exact: hSW x hx]|exact: hSA x hx].
have hTA : T `<=` A by move=> x [].
have hTU : T `<=` U by move=> x [[hx _] _].
have hTW : T `<=` W by move=> x [[_ hx] _].
exists T; split.
- apply: (@borel_family_binary_intersection _ setT _ (borel_sets_family X)); last exact hA.
  exact: (@borel_family_binary_intersection _ setT _ (borel_sets_family X) U W hU hW).
split=> //; split=> //; split; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@measure_mono R X phi hphi S T hST).
- rewrite heU; exact (@measure_mono R X phi hphi T U hTU).
- exact (@measure_mono R X psi hpsi S T hST).
- rewrite heW; exact (@measure_mono R X psi hpsi T W hTW).
Qed.
