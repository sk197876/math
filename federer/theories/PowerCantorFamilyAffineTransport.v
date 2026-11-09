(** Federer (1969), 3.3.20, pp. 307–308:
    positive similarities preserve the actual original Phi families. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge CantorSplitRadiusUP CantorSplitRadius
  EqualCostIntervalFamilyUP AffineIntervalTransportUP PositiveAffineClosedSegment
  PowerCantorSplitScale RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_family_positive_affine_transport]:
    supporting actual original-square similarities in
    3.3.20, pp. 307–308. Every original
    equal-cost interval family is transported to
    the equal-cost family of its transformed parent,
    retaining every original index, endpoint and
    subdivision number. Existence and uniqueness of
    the interval transport are separate; only its
    independent exact set-image laws are used here. *)
Theorem power_cantor_family_positive_affine_transport (R:realType) (a r c m:R)
    M (J:compact_real_intervals R) n F:
  0<r ->is_affine_interval_transport a r M ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) J n F ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) (M J) n [fset M S|S in F].
Proof.
move=>hr hM [hn [l [h [s [t [hJ [hWidth [hSplit [hSpace hChildren]]]]]]]]].
have [hs hSmall]:=cantor_split_radius_bounds hSplit.
have hImage U v:val U=v ->val (M U)=(fun x:R=>a+r * x) @` v by move=>hU;rewrite hM hU.
have hRoot:val (M J)=(`[a+r * l,a+r * h]:set (real_line_metric R)).
  by rewrite hM hJ positive_affine_closed_segment_image.
have hParent:(a+r * h)-(a+r * l)=r * (h-l) by ring.
have hParentPositive:0<(a+r * h)-(a+r * l) by rewrite hParent;exact:mulr_gt0 hr hWidth.
have hSplitScaled:=@power_cantor_split_positive_scale R c m (h-l) s r n hr hWidth hSplit.
have hSpacing:r * t=cantor_split_spacing ((a+r * h)-(a+r * l)) n (r * s).
  rewrite hSpace hParent /cantor_split_spacing;ring.
have hLeft i:a+r * (l+i%:R * t)=(a+r * l)+i%:R * (r * t) by ring.
have hRight i:a+r * (l+i%:R * t+s)=(a+r * l)+i%:R * (r * t)+r * s by ring.
split=>//;exists (a+r * l),(a+r * h),(r * s),(r * t).
split=>//;split=>//;split;first by rewrite hParent.
split=>//;move=>U;split.
- move=>/imfsetP[V hV hValue].
  have [i [hi hVValue]]:=(hChildren V).1 hV.
  exists i;split=>//;rewrite hValue hM hVValue positive_affine_closed_segment_image // hLeft hRight.
  by [].
- move=>[i [hi hUValue]].
  have hOrder:l+i%:R * t<=l+i%:R * t+s by rewrite lerDl;exact:ltW hs.
  have hInterval:is_compact_real_interval (`[l+i%:R * t,l+i%:R * t+s]:set (real_line_metric R)).
    exists (l+i%:R * t),(l+i%:R * t+s);by split.
  pose V:compact_real_intervals R:=Sub (`[l+i%:R * t,l+i%:R * t+s]:set (real_line_metric R)) (mem_set hInterval).
  have hV:V \in F by apply/(hChildren V);exists i;by split.
  apply/imfsetP;exists V;first exact:hV.
  apply:val_inj;rewrite hM /V /= positive_affine_closed_segment_image // hLeft hRight.
  exact:hUValue.
Qed.
