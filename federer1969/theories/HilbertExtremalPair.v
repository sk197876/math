(** Federer (1969), 1.10.5, p. 48, supporting two-entry conclusion in the
    local proof of the Hilbert-input norm equality. An extremal unit pair
    maximizing the total-sum length among all extremal unit pairs must have
    equal entries. The argument uses polarization, normalization and the
    parallelogram identity. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear BilinearNegation InnerProductUP
  InnerNorm InnerNormInequalities InnerNormalization InnerParallelogram
  HilbertBilinearMaximizers HilbertPairGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hilbert_extremal_pair_equal]: Federer 1.10.5,
    p. 48, supporting equality of two entries in the secondary
    maximizing tuple. An opposite pair allows a strictly better equal
    pair; any other unequal pair improves after normalizing its sum. *)
Theorem hilbert_extremal_pair_equal (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (g : V -> V -> R) (hg : is_symmetric_bilinear g) M
    (hb : forall u v, `|g u v|<=M*inner_norm hB u*inner_norm hB v)
    t x y (hx : inner_norm hB x= 1) (hy : inner_norm hB y= 1)
    (he : `|g x y|=M)
    (hmax : forall u v, inner_norm hB u= 1 -> inner_norm hB v= 1 ->
      `|g u v|=M -> inner_norm hB (t+(u+v))<=inner_norm hB (t+(x+y))) : x=y.
Proof.
pose N := inner_norm hB.
have hn : N (t-(x+y))<=N (t+(x+y)).
  have hh := hmax (-x) (-y).
  rewrite !inner_normN (bilNl (proj1 hg)) (bilNr (proj1 hg)) opprK he in hh.
  have h := hh hx hy erefl; by rewrite -opprD in h.
case hs : (x+y==0).
- have hs0 : x+y=0 := elimT eqP hs.
  have hyx : y= -x by apply: (addrI x); rewrite hs0 addrN.
  have hxx : `|g x x|=M.
    by move: he; rewrite hyx (bilNr (proj1 hg)) normrN.
  have hp := hmax x x hx hx hxx.
  have hm : N (t+(-x + -x))<=N (t+(x+y)).
    apply: hmax; rewrite ?inner_normN // (bilNl (proj1 hg))
      (bilNr (proj1 hg)) opprK; exact hxx.
  rewrite hs0 addr0 in hp hm.
  have h2 : x+x=(2:R)*:x by rewrite scaler_nat mulr2n.
  rewrite h2 in hp.
  rewrite -opprD h2 in hm.
  have hbad := @hilbert_opposite_pair_improves R V B hB t x hx hp hm.
  exact: False_ind hbad.
- have hsN : x+y!=0 by rewrite hs.
  pose z := inner_normalize hB (x+y).
  pose a := N (x+y).
  have ha : 0<a by rewrite /a /N inner_norm_gt0.
  have ha2 : a<= 2.
    have hh := inner_norm_triangle hB x y; rewrite hx hy in hh.
    exact hh.
  have [hz hgz] := @symmetric_bilinear_maximizer_normalized_sum R V B hB
    g hg M hb x y hx hy he hsN.
  have hmaxz := hmax z z hz hz hgz.
  have hrec : a*:z=x+y := inner_normalizeK hB hsN.
  have h2 : z+z=(2:R)*:z by rewrite scaler_nat mulr2n.
  rewrite h2 -hrec in hmaxz hn.
  have haE : a= 2 := @hilbert_scaled_sum_maximum R V B hB t z a hz ha ha2 hn hmaxz.
  have hp := inner_parallelogram hB x y.
  rewrite hx hy !expr1n in hp.
  change (a^+2+N (x-y)^+2= 2*(1+1)) in hp.
  rewrite haE in hp.
  have hfour : (2:R)*(1+1)= 2^+2 by rewrite expr2.
  rewrite hfour in hp.
  have hd0 : N (x-y)^+2=0.
    apply: (addrI ((2:R)^+2)); by rewrite addr0 hp.
  have hd : N (x-y)=0 by apply/eqP; rewrite -sqrf_eq0 hd0 eqxx.
  rewrite /N in hd.
  apply/eqP; by rewrite -subr_eq0 -(inner_norm_eq0 hB) hd eqxx.
Qed.
