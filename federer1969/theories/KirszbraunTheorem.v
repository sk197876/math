(** Federer (1969), 2.10.43, printed p. 201: every Lipschitz map from an
    arbitrary subset of Euclidean space to Euclidean space has a global
    agreeing extension with the same optimal Lipschitz constant. The proof
    uses only the opaque extension laws and existing least-constant laws.
    The working erratum has no relevant book p. 201 entry. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic LipschitzConstant
  KirszbraunExtensionUP KirszbraunExtensionLaws KirszbraunExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_43]: direct complete
    Kirszbraun theorem of 2.10.43, p. 201.
    The global extension agrees on the exact
    original subset and has the same least
    Lipschitz constant. Empty sources, constant
    maps and either zero-dimensional space are included. *)
Theorem federer_2_10_43 (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (hLip : is_metric_lipschitz S f) :
  exists g, exists hGlobal : is_metric_lipschitz setT g,
    (forall x, S x -> g x=f x) /\ metric_lipschitz_constant hGlobal=metric_lipschitz_constant hLip.
Proof.
pose L := metric_lipschitz_constant hLip.
have hleast := metric_lipschitz_constant_specification hLip.
have hbound : is_metric_lipschitz_bound S f L := least_metric_lipschitz_bound hleast.
pose g := @euclidean_lipschitz_extension R m n S f L hbound.
have hg := @euclidean_lipschitz_extension_specification R m n S f L hbound.
have hGlobal : is_metric_lipschitz setT g := metric_lipschitz_of_bound (kirszbraun_extension_bound_law hg).
exists g,hGlobal; split; first exact: kirszbraun_extension_agreement_law hg.
exact: least_metric_lipschitz_unique (metric_lipschitz_constant_specification hGlobal)
  (kirszbraun_extension_optimal_bound hg hleast).
Qed.
