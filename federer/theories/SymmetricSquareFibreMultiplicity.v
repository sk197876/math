(** Federer (1969), 3.2.28(4), p. 267:
    the square map has exactly two points in each
    fibre of an antipodal unit-sphere subset. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal lra.
From Federer Require Import Bilinear BilinearNegation InnerProductUP InnerProductLaws InnerNorm SymmetricGrading SymmetricSquareGeometry
  CountingMeasure CountingPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_unit_antipodal_distinct]: the two
    signs of a unit vector are distinct over R,
    supporting the exact two-to-one assertion in
    Federer 3.2.28(4), p. 267. *)
Lemma inner_unit_antipodal_distinct (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) x:
  inner_norm hB x= 1 ->x!= -x.
Proof.
move=>hx; apply/eqP=>he.
have hUnit:B x x= 1 by rewrite -[B x x](inner_norm_sqr hB) hx expr1n.
have h:=congr1 (fun z=>B x z) he.
rewrite (bilNr (inner_bilinear hB)) hUnit in h; lra.
Qed.

(** Source for [inner_projective_square_fibre_pair]:
    the exact two-point inverse image in Federer
    3.2.28(4), p. 267, on every antipodal
    subset of the unit sphere. *)
Lemma inner_projective_square_fibre_pair (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (A:set V) x:
  (forall y,A y ->inner_norm hB y= 1) ->
  (forall y,A y ->A (-y)) ->A x ->
  [set y|A y /\inner_projective_square y=inner_projective_square x]=[set x] `|` [set -x].
Proof.
move=>hA hNeg hx; apply/seteqP; split=>y.
- move=>[hy hT]; exact ((@inner_projective_square_unit_fibre R V B hB y x (hA y hy) (hA x hx)).1 hT).
- move=>[->|->]; split; [exact hx|reflexivity|exact:hNeg x hx|exact:(@inner_projective_square_antipodal R V B hB x)].
Qed.

(** Source for [inner_projective_square_fibre_count]: the
    multiplicity two used in the actual area identity,
    Federer 3.2.28(4), p. 267. The count is
    proved from the exact fibre and counting laws. *)
Theorem inner_projective_square_fibre_count (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (A:set V) z:
  (forall y,A y ->inner_norm hB y= 1) ->
  (forall y,A y ->A (-y)) ->(@inner_projective_square R V @` A) z ->
  @counting_measure R V [set y|A y /\inner_projective_square y=z]=(2:R)%:E.
Proof.
move=>hA hNeg [x hx <-].
rewrite (@inner_projective_square_fibre_pair R V B hB A x hA hNeg hx).
exact (@counting_measure_distinct_pair R V x (-x)
  (@inner_unit_antipodal_distinct R V B hB x (hA x hx))).
Qed.
