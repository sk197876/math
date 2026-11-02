(** Federer (1969), 3.2.13, p. 250: actual
    fibres of y mapped to y^2
    on a bounded symmetric interval. Positive
    target values have two roots, and the
    roots stay inside exactly the squared radius. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import RealMetricBackground MappingMultiplicity SignedSquareRootSealed SignedSquareRootLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [square_symmetric_interval_fibre_pair]: the two
    inverse values in the Gamma square substitution,
    Federer 3.2.13, p. 250. The
    root witness uses only the already opaque
    signed-root laws, and is local to this existence proof. *)
Lemma square_symmetric_interval_fibre_pair (R:realType) (b y:R):
  0<b ->0<y ->y<=b^+2 ->exists q:R,0<q /\q^+2=y /\
    mapping_fibre (fun x:R=>x^+2) `[-b,b] y=[set q] `|` [set -q].
Proof.
move=>hb hy hyb.
pose q:=@SignedSquareRoot.value R y.
have hq0:0<=q:=(@signed_root_sign_bounds R y).1 (ltW hy).
have hqSquare:q^+2=y by rewrite /q signed_root_square (ger0_norm (ltW hy)).
have hqPos:0<q.
  rewrite lt_neqAle eq_sym hq0 andbT; apply/eqP=>he.
  have hBad:=hqSquare; rewrite he expr0n /= in hBad; lra.
have hqBound:q<=b by nra.
exists q; split=>//; split=>//.
apply/seteqP; split=>x /=.
- move=>[hx hSquare].
  have hCases:(x==q)||(x== -q) by rewrite -eqf_sqr hqSquare; apply/eqP.
  by case/orP:hCases=>/eqP he; [left|right].
- move=>[hx|hx]; rewrite hx; split.
  + rewrite /= in_itv /=; apply/andP; split=>//; nra.
  + exact hqSquare.
  + rewrite /= in_itv /=; apply/andP; split; nra.
  + have hNeg:(-q)^+2=q^+2 by rewrite !expr2 mulrNN.
    exact (eq_trans hNeg hqSquare).
Qed.

(** Source for [square_symmetric_interval_fibre_empty]: square
    values on [-b,b] lie in [0,b^2],
    supporting the actual multiplicity computation for
    the Gamma substitution, Federer 3.2.13, p. 250. *)
Lemma square_symmetric_interval_fibre_empty (R:realType) (b y:R):
  0<b ->(y<0 \/b^+2<y) ->
  mapping_fibre (fun x:R=>x^+2) `[-b,b] y=set0.
Proof.
move=>hb hy; apply/seteqP; split=>x; last by [].
move=>[hx hSquare]; move:hx; rewrite /= in_itv /= =>/andP[hLow hHigh].
have hAbs:`|x|<=b by rewrite ler_norml; apply/andP; split.
have hSqr:x^+2<=b^+2.
  have h:=lerXn2r 2 (normr_ge0 x) (ltW hb) hAbs.
  by rewrite -normrX ger0_norm ?sqr_ge0 in h.
have hNonnegative:=sqr_ge0 x.
rewrite hSquare in hSqr hNonnegative.
case:hy=>h.
- by have hBad:=lt_le_trans h hNonnegative; rewrite ltxx in hBad.
- by have hBad:=lt_le_trans h hSqr; rewrite ltxx in hBad.
Qed.
