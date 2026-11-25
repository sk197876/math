(** Federer (1969), 2.9.18(2), p. 163: a witness p in O*(n,1), with n= 2 in
    the printed example. The coordinate projection formula and O* are from
    1.7.4, pp. 30–31. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import GrassmannAbbreviations ExteriorIndices CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [single_coordinate_selection]: supporting
    projection witness for Federer 2.9.18(2), p. 163:
    the increasing singleton coordinate selection for p_lambda
    in 1.7.4, p. 31. *)
Definition single_coordinate_selection n (i : 'I_n) : Lambda n 1 :=
  Sub [tuple i] (erefl true).

(** Source for [single_coordinate_projection_value]: supporting
    O*(n,1) projection formula for Federer 2.9.18(2),
    p. 163, from the selected-coordinate formula of
    1.7.4, p. 31. The only output coordinate is x_i. *)
Lemma single_coordinate_projection_value (R : realFieldType) n (i : 'I_n)
    (x : R_n R n) (k : 'I_1) :
  coordinate_projection (single_coordinate_selection i) x k=x i.
Proof. by rewrite coordinate_projectionE /single_coordinate_selection /= (ord1 k) tnth0. Qed.

(** Source for [single_coordinate_projection_orthogonal]: the
    O* hypothesis in Federer 2.9.18(2), p. 163,
    satisfied by the singleton coordinate projection of 1.7.4,
    p. 31. It is a proved witness, not an
    additional assumption on the example. *)
Lemma single_coordinate_projection_orthogonal (R : realFieldType) n (i : 'I_n) :
  O_star (GRing.Linear.clone _ _ _ _
    (@coordinate_projection R n 1 (single_coordinate_selection i)) _).
Proof. exact: coordinate_projection_orthogonal. Qed.
