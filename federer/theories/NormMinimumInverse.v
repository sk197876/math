(** Federer (1969), 3.1.1, p. 209: reciprocal inverse norm is the
    minimum expansion of an invertible continuous linear map. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormUnitSphereBounds
  NormMinimumModulusUP NormOperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_minimum_inverse]: the sentence following the two
    limit identities in Federer 3.1.1, p. 209: when the differential has
    a continuous inverse, the unit-sphere infimum is the reciprocal of
    its inverse's operator norm. The nonzero-source condition excludes
    the empty unit sphere, whose infimum is infinite (2.1.1, p. 51). *)
Theorem norm_minimum_inverse (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) (M : Hom Y X) (m n : R) :
  (exists x : X, x != 0) ->
  (forall x, M (L x) = x) -> (forall y, L (M y) = y) ->
  is_norm_minimum_modulus NX NY L m ->
  is_norm_operator_norm NY NX M n -> 0 < n /\ m = n^-1.
Proof.
move=> hX hML hLM hm hn.
have [u hu] := norm_unit_direction_exists hNX hX.
have hb := norm_operator_bound hn (L u); rewrite hML hu in hb.
have hn0 := norm_operator_nonnegative hn.
have hLu := real_seminorm_nonnegative hNY.1 (L u).
have hnpos : 0 < n by nra.
have hnneq := lt0r_neq0 hnpos.
have hninv : n*n^-1 = 1 by rewrite mulfV.
have hinv : 0 < n^-1 by rewrite invr_gt0.
have hlower : forall x, n^-1*NX x <= NY (L x).
  move=> x; have hx := norm_operator_bound hn (L x); rewrite hML in hx.
  by rewrite mulrC ler_pdivrMr // mulrC.
have hmin := norm_minimum_greatest hm hlower.
have hmpos : 0 < m := lt_le_trans hinv hmin.
have hmneq := lt0r_neq0 hmpos.
have hminv : m * m^-1 = 1 by rewrite mulfV.
have hupper : forall y, NX (M y) <= m^-1*NY y.
  move=> y; have hy := norm_minimum_bound hm (M y); rewrite hLM in hy.
  by rewrite mulrC ler_pdivlMr // mulrC.
have him0 : 0 <= m^-1 by rewrite invr_ge0; exact: ltW hmpos.
have hnle := norm_operator_least hn him0 hupper.
have hmnle : m*n <= 1.
  have h := ler_wpM2l (ltW hmpos) hnle.
  by rewrite hminv in h.
have hmnge : 1 <= m*n.
  have h := ler_wpM2r (ltW hnpos) hmin.
  by rewrite mulVf // in h.
have heq : m*n = 1 by apply/eqP; rewrite eq_le hmnle hmnge.
split=> //.
by apply: (mulIf hnneq); rewrite heq mulVf.
Qed.
