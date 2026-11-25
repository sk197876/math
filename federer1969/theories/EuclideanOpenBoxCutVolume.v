(** Federer (1969), 3.2.41, printed p. 277, finite-family
    proof: cutting a box multiplies its other side lengths by
    the clipped length of the selected coordinate interval. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes LebesgueScalarMeasure
  MeasureUP EuclideanOpenCoordinateBoxUP ScalarOpenIntervalCuts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_coordinate_box_left_cut_volume]: supporting
    actual coordinate-cut mass used to choose b in Federer 3.2.41,
    p. 277. Cuts outside and at original endpoints are included;
    no cut measurability or volume formula is assumed. *)
Lemma open_coordinate_box_left_cut_volume (R:realType) n (a b:R_n R n)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t:R):
  is_euclidean_open_coordinate_box a b A ->
  @euclidean_lebesgue_measure R n (A `&` [set x|x k<t])=
    (Order.max 0 (Order.min (b k) t-a k)*(\prod_(i | i!=k) (b i-a i)))%R%:E.
Proof.
move=> hA.
pose D i:set R:=if i==k then `]a i,b i[ `&` [set x:R|x<t] else `]a i,b i[.
have hD i:measure_measurable (@lebesgue_scalar_measure R) (D i).
  rewrite /D; case:(i==k); first exact:scalar_interval_left_cut_measurable.
  exact:lebesgue_scalar_open_interval_measurable.
have hEq:A `&` [set x|x k<t]=euclidean_coordinate_box D.
  apply/seteqP; split=> x.
  - move=> [hx hCut] i; have hi:=(hA.2 x).1 hx i.
    rewrite /D; case:(eqVneq i k)=>[->|hNe].
    + split=>//; by rewrite /= in_itv; exact:(hA.2 x).1 hx k.
    + by rewrite /= in_itv.
  - move=> hx; split.
    + apply:(hA.2 x).2=> i.
      have hi:=hx i; rewrite /D in hi.
      case:(i==k) in hi.
      * have hi':=hi.1; by move:hi'; rewrite /= in_itv.
      * by move:hi; rewrite /= in_itv.
    + have hi:=hx k; by rewrite /D eqxx in hi; exact hi.2.
have [_ hVolume]:=@euclidean_coordinate_box_measure R n D hD.
rewrite hEq hVolume (bigD1 k) //= /D eqxx
  (scalar_interval_left_cut_length t (hA.1 k)).
have hRest:(\prod_(i | i!=k) @lebesgue_scalar_measure R (D i))%E=
    (\prod_(i | i!=k) (b i-a i))%R%:E.
  rewrite -prodEFin; apply:eq_bigr=> i hNe.
  by rewrite /D (negbTE hNe) (lebesgue_scalar_open_interval (ltW (hA.1 i))).
by rewrite hRest -EFinM.
Qed.
