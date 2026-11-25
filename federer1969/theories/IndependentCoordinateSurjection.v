(** Federer (1969), 3.4.5, p. 321: the independent
    defining differentials give full rank. Reuse the actual
    biorthogonal vectors of 1.4.3, p. 19; no
    new extension or matrix construction is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom Bilinear FiniteIndependence Biorthogonal GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [independent_coordinate_surjection]: full target
    rank of the defining map in 3.4.5, p. 321,
    used for the analytic charts in 3.4.8(12),
    pp. 327, 335. The coordinate differentials are
    the original independent covectors. *)
Theorem independent_coordinate_surjection (K:realFieldType) (X:lmodType K) q
    (D:'I_q->Hom X K^o) (L:Hom X (R_n K q)):
  finite_independent D ->(forall x i,L x i=D i x) ->
  forall y,exists x,L x=y.
Proof.
move=>hD hL y.
have [e he]:=biorthogonal_exists hD.
exists (\sum_j y j*:e j);apply/ffunP=>i.
rewrite hL.
change ((D i) (\sum_j y j*:e j)=y i).
rewrite linear_sum.
under eq_bigr do rewrite linearZ.
change ((\sum_j y j*D i (e j))=y i).
under eq_bigr do rewrite he.
rewrite (bigD1 i) //= eqxx mulr1.
have hZero:(\sum_(j | j!=i) y j*(if i==j then 1 else 0))=0.
  apply:big1=>j hji;have hij:i!=j by rewrite eq_sym.
  by rewrite (negbTE hij) mulr0.
by rewrite hZero addr0.
Qed.
