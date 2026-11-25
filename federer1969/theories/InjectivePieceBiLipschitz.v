(** Federer (1969), 4.1.25, p. 383: use
    the pieces of 3.2.2, p. 242, with
    the two-sided metric estimates needed in 3.2.17,
    p. 254. Reuse the already proved ordinary
    forward and inverse restrictions from 3.2.9,
    p. 247, and increase their two bounds to
    a single positive bound. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric LipschitzUP LipschitzBasic MetricBiLipschitzUP
  InjectiveDifferentialPieceUP InjectivePieceLipschitzRestrictions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [injective_piece_bilipschitz_bound]: each
    original piece in Federer 3.2.2, p. 242,
    admits the common positive forward/inverse bound
    used in the proof of 4.1.25, p. 383.
    No extension or global injectivity of the
    original map is added. *)
Theorem injective_piece_bilipschitz_bound (R : realType) m n
    (f : R_n R m -> R_n R n) (lambda : R)
    (E : set (R_n R m)) :
  is_injective_differential_piece f lambda E ->
  exists L : R, 0 < L /\ @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) E f L.
Proof.
move=> hPiece.
have [[A [hA hForward]] [g [[B [hB hInverse]] hRecover]]] :=
  injective_piece_forward_inverse_lipschitz hPiece.
pose L := Order.max A B.
have hAL : A <= L by rewrite /L le_max lexx.
have hBL : B <= L by rewrite /L le_max lexx orbT.
exists L; split; first exact: lt_le_trans hA hAL.
split; first exact: metric_lipschitz_bound_increase hForward hAL.
move=> x y hx hy.
have hFx : (f @` E) (f x) by exists x.
have hFy : (f @` E) (f y) by exists y.
have h := hInverse.2 (f x) (f y) hFx hFy.
rewrite (hRecover x hx) (hRecover y hy) in h.
have hDistance : 0 <= mdist
    (f x : inner_metric_space (@euclidean_inner_productP R n)) (f y).
  exact: mdist_ge0.
have hScale := ler_wpM2r hDistance hBL.
exact: le_trans h hScale.
Qed.
