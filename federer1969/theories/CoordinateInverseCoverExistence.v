(** Federer (1969), 3.2.9, p. 247: the
    countable union over the finite family of
    complementary coordinate projections. Apply 3.2.2 to
    each continuous stacked map and extend the
    forward and inverse restrictions as prescribed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality topology.
From Federer Require Import Hom GrassmannAbbreviations ExteriorIndices EuclideanInnerProduct InnerNorm NormClassOneUP
  CoordinateInverseCoverUP CoordinateStackLocus CoordinateStackPieces EuclideanStackedContinuity
  InjectiveDifferentialPieceUP InjectiveDifferentialCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_inverse_cover_complementary_dimensions]:
    the finite union of countable G_lambda in
    the proof of Federer 3.2.9, p. 247.
    The source m=n+k covers every n<=m;
    neither block is required to be positive. *)
Theorem coordinate_inverse_cover_complementary_dimensions (R:realType) n k
    (f:R_n R (n+k)->R_n R n):
  norm_class_zero (inner_norm (@euclidean_inner_productP R (n+k)))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  exists G,is_coordinate_inverse_cover f G.
Proof.
move=>hf.
have hExists (lambda:Lambda (n+k) k):exists F,
    is_injective_differential_cover (coordinate_stack_map f lambda) 2 F.
  have hClass:=@euclidean_stacked_class_zero R (n+k) n k f
    (@coordinate_projection_hom R (n+k) k lambda) hf.
  exact (injective_differential_borel_cover_exists hClass (ltr1n R 2)).
have [F hF]:=choice hExists.
pose G:=\bigcup_(lambda in (setT:set (Lambda (n+k) k))) F lambda.
exists G; split.
- apply:bigcup_countable; first exact:countableP.
  move=>lambda _; exact (hF lambda).1.
- split.
  + move=>a ha.
    have [lambda hStack]:=surjective_differential_coordinate_stack_cover ha.
    have hUnion:(\bigcup_(E in F lambda) E) a by rewrite (hF lambda).2.1.
    have [E hE haE]:=hUnion.
    exists E; last exact haE.
    exists lambda=>//.
  + move=>E [lambda _ hE].
    exact (coordinate_stack_piece_laws ((hF lambda).2.2 E hE)).
Qed.
