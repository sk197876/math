(** Federer (1969), 3.2.32, p. 269: supporting rank
    meaning of a zero actual exterior norm in the alternative
    of 3.2.22(1), p. 258. Use the rank/exterior equivalence
    of 3.1.18, p. 229, and the actual operator-norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanLinearJacobian LinearRankAtLeast LinearRankExterior
  ExteriorMaps ExteriorOperatorNorm OperatorNormUP OperatorNormLaws ExteriorRankZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_exterior_jacobian_zero_iff_low_rank]: supporting
    interpretation of the zero-Jacobian alternative for Federer
    3.2.32, p. 269. In every exterior degree, the actual
    operator norm is zero exactly when the linear image has
    rank below that degree. The degree-zero zero-norm premise
    is impossible; no source/target dimension bound is added. *)
Theorem euclidean_exterior_jacobian_zero_iff_low_rank (R:realType) m n q
    (H:Hom (R_n R m) (R_n R n)):
  euclidean_linear_jacobian q H=0 <->~linear_rank_at_least H q.
Proof.
split; last exact:euclidean_exterior_jacobian_rank_zero.
move=>hZero hRank.
have hNorm:=exterior_operator_normP (euclidean_two_nonzero R)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (@coordinate_basisP R m) (hom_as_linear H) q.
have hMapZero:=(operator_norm_zero_iff hNorm).1 hZero.
have [xi hNonzero]:=(linear_rank_exteriorP (euclidean_two_nonzero R)
  (@coordinate_basisP R m) H q).1 hRank.
by move:hNonzero; rewrite hMapZero eqxx.
Qed.
