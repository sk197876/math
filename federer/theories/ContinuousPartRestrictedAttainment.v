(** The bounded-parent Borel set chosen in Federer (1969), 2.9.2, p. 153.
    Source context: AbsoluteContinuousPartUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import AbsoluteContinuousPartUP AbsoluteContinuousPartAttainment
  MeasureUP MeasureBasic MeasureAlmostBasic TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_attained_inside]: the
    Borel subset B of a bounded Borel A in the proof
    of Federer 2.9.2, p. 153. This supporting
    attainment statement works inside an arbitrary Borel parent;
    boundedness is required later for finite cancellation. *)
Theorem continuous_part_attained_inside (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) (A S : set X) :
  is_measure phi -> is_measure psi -> is_absolutely_continuous_part phi psi gamma ->
  borel_set A -> S `<=` A -> exists B,
    borel_set B /\ B `<=` A /\ phi (S `\` B)=0 /\ gamma S=psi B.
Proof.
move=> hphi hpsi hg hA hSA.
have [C [hC [hz he]]] := @continuous_part_attained R X phi psi gamma hphi hpsi hg S.
pose B := C `&` A.
have hB : borel_set B := @borel_family_binary_intersection _ setT _ (borel_sets_family X) C A hC hA.
have hBA : B `<=` A by move=> x [].
have hnull : phi (S `\` B)=0.
  apply: (@measure_null_subset R X phi hphi _ (S `\` C)) hz.
  move=> x [hx hnB]; split=> // hC'; apply: hnB; split=> //; exact: hSA x hx.
exists B; split=> //; split=> //; split=> //; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@continuous_part_lower R X phi psi gamma hg S B hB hnull).
- rewrite he; apply: (@measure_mono R X psi hpsi B C); by move=> x [].
Qed.
