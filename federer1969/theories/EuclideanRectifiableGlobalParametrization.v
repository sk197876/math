(** Federer (1969), 3.2.18, p. 255:
    combine the positive-degree parametrization
    of 3.2.14 with the proved extension
    theorem 2.10.43. The original bounded
    domain may be nonmeasurable and partial. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialMetricLipschitz PartialFunctionExtensionUP PartialFunctionExtensionSealed
  LipschitzUP LipschitzBasic CoveringFamilyUP RectifiableSetUP
  KirszbraunExtensionUP KirszbraunExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_rectifiable_global_parametrization]:
    the reduction to a global Lipschitz
    parametrization in Federer 3.2.18,
    p. 255. Positive source degree is
    explicit because zero rectifiable means finite
    and one R^0 map has only one image point. *)
Theorem positive_rectifiable_global_parametrization (R : realType) m n
    (F : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_m_rectifiable m.+1 F ->
  exists (A : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (g : inner_metric_space (@euclidean_inner_productP R m.+1) ->
      inner_metric_space (@euclidean_inner_productP R n)),
    metric_set_bounded A /\ is_metric_lipschitz setT g /\ g @` A=F.
Proof.
move=> [f [hA [[L hLip] hRange]]].
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose A := partial_function_domain f.
pose f0 := @PartialFunctionExtension.value X Y f 0.
have hExt := @PartialFunctionExtension.laws X Y f 0.
have hBound : is_metric_lipschitz_bound A f0 L.
  split; first exact hLip.1.
  move=> x y [u hxu] [v hyv].
  rewrite /f0 (hExt x u hxu) (hExt y v hyv).
  exact: (hLip.2 x y u v hxu hyv).
pose g := @euclidean_lipschitz_extension R m.+1 n A f0 L hBound.
have hg := @euclidean_lipschitz_extension_specification R m.+1 n A f0 L hBound.
exists A,g; split=> //; split.
- exact: metric_lipschitz_of_bound (kirszbraun_extension_bound_law hg).
- rewrite -hRange; apply/seteqP; split=> y.
  + move=> [x hx <-]; have [z hz] := hx.
    exists x; rewrite (@kirszbraun_extension_agreement_law R m.+1 n A f0 g L hg x hx) /f0 (hExt x z hz); exact hz.
  + move=> [x hxy]; exists x; first by exists y.
    rewrite (@kirszbraun_extension_agreement_law R m.+1 n A f0 g L hg x ltac:(by exists y)).
    exact: hExt x y hxy.
Qed.
