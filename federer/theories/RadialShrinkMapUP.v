(** Federer (1969), 4.1.15, p. 372:
    the printed radial shrink map is specified by its
    two value laws before existence and Lipschitz bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import RealNormUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section RadialShrinkMapUP.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N :=
  (inner_norm (@euclidean_inner_productP R n)).

(** Source for [is_radial_shrink_map]: the two defining
    formulas for Psi_r in Federer 4.1.15, p. 372.
    Inside the radius it is zero; on and beyond the
    boundary it equals (1-r/|y|)y. Bounds and existence
    are consequences proved separately, not assumptions. *)
Record is_radial_shrink_map (r : R) (P : X -> X) : Prop := {
  (** Source for [radial_shrink_inner]: Psi_r(y)=0
      for |y|<r, Federer 4.1.15, p. 372. *)
  radial_shrink_inner : forall y, N y < r -> P y = 0;
  (** Source for [radial_shrink_outer]: the printed
      formula (1-r/|y|)y for |y|>=r, Federer
      4.1.15, p. 372. The intended radius is positive. *)
  radial_shrink_outer : forall y,
    r <= N y -> P y = (1-r/N y) *: y
}.

(** Source for [radial_shrink_map_unique]: the two
    exhaustive defining cases determine the original map
    in Federer 4.1.15, p. 372. Dimension zero is allowed. *)
Theorem radial_shrink_map_unique r (P Q : X -> X) :
  is_radial_shrink_map r P -> is_radial_shrink_map r Q -> P = Q.
Proof.
move=> hP hQ; apply: funext => y.
case: (ltP (N y) r) => hy.
- by rewrite (radial_shrink_inner hP hy) (radial_shrink_inner hQ hy).
- by rewrite (radial_shrink_outer hP hy) (radial_shrink_outer hQ hy).
Qed.
End RadialShrinkMapUP.
