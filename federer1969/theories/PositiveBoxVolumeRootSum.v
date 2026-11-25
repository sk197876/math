(** Federer (1969), 3.2.41, printed p. 277, first proof display:
    normalize each interval length by the length of its sum interval.
    This supporting scalar form retains the actual interval lengths;
    the normalizing volume and its root are proved positive. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower FiniteArithmeticGeometricMean.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_box_volume_root_sum]: supporting box case
    of Federer 3.2.41, p. 277. The root of the product of the summed
    positive side lengths bounds the sum of the two original product
    roots. Positive dimension is explicit, as required by 1/n. *)
Theorem positive_box_volume_root_sum (R : realType) n (l m : 'I_n -> R) :
  (0<n)%N -> (forall i, 0<l i) -> (forall i, 0<m i) ->
  real_power (\prod_i l i) (n%:R)^-1+
    real_power (\prod_i m i) (n%:R)^-1 <=
  real_power (\prod_i (l i+m i)) (n%:R)^-1.
Proof.
move=> hn hl hm.
pose w i := l i+m i.
pose u i := l i/w i.
pose v i := m i/w i.
have hw i : 0<w i by rewrite /w; have := hl i; have := hm i; lra.
have hw0 i : w i!=0 by rewrite gt_eqF.
have hu i : 0<=u i := divr_ge0 (ltW (hl i)) (ltW (hw i)).
have hv i : 0<=v i := divr_ge0 (ltW (hm i)) (ltW (hw i)).
have huv i : u i+v i=(1:R) by rewrite /u /v -mulrDl -/(w i) divff.
have hMean := complementary_product_root_bound hn hu hv huv.
have hProdL : (\prod_i l i)=(\prod_i u i)*(\prod_i w i).
  rewrite -big_split; apply: eq_bigr=> i _.
  change (l i=(l i/w i)*w i); by rewrite divfK.
have hProdM : (\prod_i m i)=(\prod_i v i)*(\prod_i w i).
  rewrite -big_split; apply: eq_bigr=> i _.
  change (m i=(m i/w i)*w i); by rewrite divfK.
have huProd : 0<=\prod_i u i by apply: prodr_ge0=> i _; exact: hu.
have hvProd : 0<=\prod_i v i by apply: prodr_ge0=> i _; exact: hv.
have hwProd : 0<=\prod_i w i by apply: prodr_ge0=> i _; exact: ltW (hw i).
rewrite hProdL hProdM !real_power_product // -mulrDl.
have h := ler_wpM2r (real_power_nonnegative (\prod_i w i) (n%:R)^-1) hMean.
by rewrite mul1r in h.
Qed.
