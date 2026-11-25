(** Federer (1969), 3.2.9, p. 247: each
    Borel distortion piece of U_lambda has the
    printed coordinate projection and global Lipschitz
    maps. Their prescribed values are only on E. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations ExteriorIndices CoordinateProjection EuclideanInnerProduct InnerMetric
  CoordinateInverseCoverUP InjectiveDifferentialPieceUP CoordinateStackLocus EuclideanStackedMap
  BorelInjectivePieceExtensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_stack_piece_laws]: the
    last paragraph of the proof of Federer
    3.2.9, p. 247. Use 3.2.2 and
    Kirszbraun to obtain both global maps while
    keeping the original coordinate projection in O*. *)
Lemma coordinate_stack_piece_laws (R:realType) n k
    (f:R_n R (n+k)->R_n R n) (lambda:Lambda (n+k) k) (distortion:R) E:
  is_injective_differential_piece (coordinate_stack_map f lambda) distortion E ->
  is_coordinate_inverse_piece f E.
Proof.
move=>hPiece.
have [hB [u [v [hU [hV hAgree]]]]]:=borel_injective_piece_global_extensions hPiece.
rewrite /is_coordinate_inverse_piece addKn.
split; first exact hB.
exists (GRing.Linear.clone _ _ _ _ (@coordinate_projection R (n+k) k lambda) _).
split; first exact:coordinate_projection_orthogonal.
exists u,v; split; first exact hU; split; first exact hV.
move=>x hx; have [hFirst hLast]:=hAgree x hx.
split; last exact hLast.
rewrite hFirst /coordinate_stack_map euclidean_stacked_join.
exact:erefl.
Qed.
