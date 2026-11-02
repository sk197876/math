(** Federer (1969), 3.2.39, p. 275: a closed
    genuinely rectifiable positive-degree set is an actual compact
    image of one globally Lipschitz map. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP EuclideanRectifiableGlobalParametrization MetricBoundedClosureLaws
  LipschitzUP NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_positive_rectifiable_compact_parametrization]:
    the first paragraph of the proof of Federer 3.2.39,
    p. 275. Extend the original partial parametrization through
    the earlier opaque same-bound extension, close its bounded
    source and restrict to the exact preimage of the original
    closed W. Neither its closure nor a larger image replaces W.
    Positive degree is explicit: zero rectifiable finite sets may
    contain several atoms and are treated separately. *)
Theorem closed_positive_rectifiable_compact_parametrization (R:realType) m n
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):
  closed W ->is_m_rectifiable m.+1 W ->
  exists (f:inner_metric_space (@euclidean_inner_productP R m.+1)->
    inner_metric_space (@euclidean_inner_productP R n))
    (A:set (inner_metric_space (@euclidean_inner_productP R m.+1))),
    is_metric_lipschitz setT f /\compact A /\f @` A=W.
Proof.
move=>hClosed hW.
have [B [f [hB [hLip hImage]]]]:=positive_rectifiable_global_parametrization hW.
pose X:=inner_metric_space (@euclidean_inner_productP R m.+1).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hf:continuous (f:X->Y).
  have [L [hL hBound]]:=hLip.
  apply:(@metric_fixed_lipschitz_continuous R X Y f L hBound.1)=>x y.
  exact:hBound.2 x y Logic.I Logic.I.
pose A:=closure B `&` (f @^-1` W).
have hA:compact A.
  have hPreimage:closed (f @^-1` W):=(continuous_closedP f).1 hf W hClosed.
  exact:(compact_closedI (euclidean_bounded_closure_compact hB) hPreimage).
exists f,A; split=>//; split=>//; apply/seteqP; split.
- by move=>y [x [_ hx] <-].
- move=>y hy.
  have hPreimage:(f @` B) y by rewrite hImage.
  have [x hx hfx]:=hPreimage.
  exists x; last exact hfx.
  split; first exact:subset_closure hx.
  change (W (f x)); by rewrite hfx.
Qed.
