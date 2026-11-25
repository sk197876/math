(** Federer (1969), 4.1.27, p. 384:
    every strictly positive barycentric family has
    cube coordinates. Its successive positive tail
    sums give the ratios x_i=q_i/q_(i-1).
    This finite algebra uses no independence
    of the original vertices. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOpenUnitCube SimplexCubeParametrisationUP
  SimplexCubeBarycentricCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_barycentric_tail]: the remaining
    coefficient sum after the first k vertices,
    in the inverse of the displayed
    parametrisation of 4.1.27, p. 384. *)
Definition positive_barycentric_tail (R:realType) m
    (t:'I_(m.+1)->R) k:R:=
  \sum_(i:'I_(m.+1) | (k<=i)%N) t i.

(** Source for [positive_barycentric_tail_zero]: the first
    tail equals the full barycentric normalization
    in 4.1.27, p. 384. *)
Lemma positive_barycentric_tail_zero (R:realType) m (t:'I_(m.+1)->R):
  positive_barycentric_tail t 0%N=\sum_i t i.
Proof. by rewrite /positive_barycentric_tail;apply:eq_bigl=>i;rewrite leq0n. Qed.

(** Source for [positive_barycentric_tail_last]: the last
    tail is the coefficient of u_m,
    supporting 4.1.27, p. 384. *)
Lemma positive_barycentric_tail_last (R:realType) m (t:'I_(m.+1)->R):
  positive_barycentric_tail t m=t ord_max.
Proof.
rewrite /positive_barycentric_tail.
apply:big_pred1=>i.
apply/idP/eqP=>[h|->].
- apply:val_inj;apply:anti_leq;by rewrite h andbT /= -ltnS ltn_ord.
- by rewrite /= leqnn.
Qed.

(** Source for [positive_barycentric_tail_step]: extracting the
    first coefficient from a tail gives
    q_k=t_k+q_(k+1), supporting the original
    inverse-coordinate argument in 4.1.27, p. 384. *)
Lemma positive_barycentric_tail_step (R:realType) m (t:'I_(m.+1)->R) k
    (hK:(k<m.+1)%N):
  positive_barycentric_tail t k=
    t (Ordinal hK)+positive_barycentric_tail t k.+1.
Proof.
rewrite /positive_barycentric_tail (bigD1 (Ordinal hK)) /=;last exact:leqnn.
congr (t (Ordinal hK)+_);apply:eq_bigl=>i.
rewrite -val_eqE /=.
change (((k<=val i)%N)&&(val i!=k)=(k<val i)%N).
by rewrite ltn_neqAle eq_sym andbC.
Qed.

(** Source for [positive_barycentric_tail_positive]: every original
    tail is positive, including the last
    one and the single m=0 tail,
    in 4.1.27, p. 384. *)
Lemma positive_barycentric_tail_positive (R:realType) m (t:'I_(m.+1)->R):
  (forall i,0<t i)->forall k,(k<=m)%N->0<positive_barycentric_tail t k.
Proof.
move=>hPositive k hK.
have hOrdinal:(k<m.+1)%N:=leq_ltn_trans hK (ltnSn m).
rewrite (@positive_barycentric_tail_step R m t k hOrdinal).
apply:ltr_pwDl;first exact:hPositive.
rewrite /positive_barycentric_tail;apply:sumr_ge0=>i _;exact:ltW (hPositive i).
Qed.

(** Source for [positive_barycentric_cube_inverse]: the original
    inverse cube coordinates, supporting the exact
    image assertion in 4.1.27, p. 384.
    Ratios are only used under the
    separately proved positive-tail hypotheses. *)
Definition positive_barycentric_cube_inverse (R:realType) m
    (t:'I_(m.+1)->R):R_n R m:=
  [ffun i=>positive_barycentric_tail t (val i).+1/
    positive_barycentric_tail t (val i)].

(** Source for [positive_barycentric_cube_inverse_in_cube]: all
    inverse coordinates lie strictly between zero
    and one, in 4.1.27, p. 384.
    No inhabitance of the coordinate family
    is required at m=0. *)
Theorem positive_barycentric_cube_inverse_in_cube (R:realType) m
    (t:'I_(m.+1)->R):
  (forall i,0<t i)->
  euclidean_open_unit_cube (positive_barycentric_cube_inverse t).
Proof.
move=>hPositive i.
have hBefore:=@positive_barycentric_tail_positive R m t hPositive (val i)
  (ltnW (ltn_ord i)).
have hAfter:=@positive_barycentric_tail_positive R m t hPositive (val i).+1
  (ltn_ord i).
apply/andP;split.
- rewrite /positive_barycentric_cube_inverse ffunE;exact:divr_gt0 hAfter hBefore.
- rewrite /positive_barycentric_cube_inverse ffunE ltr_pdivrMr // mul1r.
  rewrite (@positive_barycentric_tail_step R m t (val i)
    (leq_ltn_trans (ltnW (ltn_ord i)) (ltnSn m))) ltrDr.
  exact:hPositive.
Qed.

(** Source for [positive_barycentric_cube_inverse_prefix]: the
    prefix products recover the positive tail
    sums, which is the cancellation underlying
    the inverse in 4.1.27, p. 384.
    The proof includes the empty prefix. *)
Theorem positive_barycentric_cube_inverse_prefix (R:realType) m
    (t:'I_(m.+1)->R):
  (forall i,0<t i)->(\sum_i t i)= 1->
  forall k,(k<=m)%N->
    simplex_cube_prefix_product (positive_barycentric_cube_inverse t) k=
      positive_barycentric_tail t k.
Proof.
move=>hPositive hSum k;elim:k=>[|k ih] hK.
- by rewrite simplex_cube_prefix_zero positive_barycentric_tail_zero hSum.
- have hPrevious:(k<=m)%N:=leq_trans (leqnSn k) hK.
  have hStep:(k<m)%N:=hK.
  rewrite (@simplex_cube_prefix_successor R m
      (positive_barycentric_cube_inverse t) k hStep)
    /positive_barycentric_cube_inverse ffunE (ih hPrevious).
  rewrite divfK;first by [].
  exact:lt0r_neq0 (@positive_barycentric_tail_positive R m t hPositive k hPrevious).
Qed.

(** Source for [positive_barycentric_cube_inverse_coefficients]: the
    cube coefficients recover every original positive
    barycentric coefficient, proving the converse image
    inclusion in 4.1.27, p. 384. *)
Theorem positive_barycentric_cube_inverse_coefficients (R:realType) m
    (t:'I_(m.+1)->R):
  (forall i,0<t i)->(\sum_i t i)= 1->
  forall i,simplex_cube_barycentric_coefficient
    (positive_barycentric_cube_inverse t) i=t i.
Proof.
move=>hPositive hSum i;rewrite /simplex_cube_barycentric_coefficient.
case hI:(i<m)%N.
- rewrite (@positive_barycentric_cube_inverse_prefix R m t hPositive hSum
      (val i) (ltnW hI))
    (@positive_barycentric_cube_inverse_prefix R m t hPositive hSum
      (val i).+1 hI)
    (@positive_barycentric_tail_step R m t (val i) (ltn_ord i))
    addrK.
  congr (t _);apply:val_inj;by [].
- have hLower:(m<=val i)%N by rewrite leqNgt hI.
  have hIndex:val i=m.
    apply:anti_leq;apply/andP;split;[rewrite -ltnS;exact:ltn_ord|exact:hLower].
  rewrite (@positive_barycentric_cube_inverse_prefix R m t hPositive hSum m (leqnn m))
    positive_barycentric_tail_last.
  congr (t _);apply:val_inj;exact:esym hIndex.
Qed.
