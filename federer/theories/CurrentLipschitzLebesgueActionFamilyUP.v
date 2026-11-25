(** Federer (1969), 4.1.25, p. 383: the smooth
    approximants in the first proof converge uniformly to f
    and boundedly almost everywhere in their differentials.
    This specification precedes their construction from 4.1.2,
    p. 347. It makes no assertion outside the original
    differential graph and imposes no full-rank qualification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness EuclideanHomOperator EuclideanLebesgueDimensions
  MeasureAlmostUP CurrentMapDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_current_lipschitz_lebesgue_action_family]:
    the original smooth approximation and bounded differential
    convergence in the proof of 4.1.25, p. 383.
    L is a proved nonnegative Lipschitz bound, not an
    additional regularity assumption on f. All natural source
    and target dimensions remain in the specification. *)
Record is_current_lipschitz_lebesgue_action_family (R:realType) m n
    (f:R_n R m->R_n R n) (L:R)
    (g:nat->R_n R m->R_n R n) : Prop := {
  (** Source: 4.1.25, p. 383; a nonnegative
      bound controls the original bounded approximation. *)
  current_lipschitz_lebesgue_action_family_nonnegative : 0<=L;
  (** Source: 4.1.25, p. 383, using the
      smooth regularization of 4.1.2, p. 347. *)
  current_lipschitz_lebesgue_action_family_smooth : forall i,
    norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT (g i);
  (** Source: 4.1.2, p. 347; normalized
      positive smoothing preserves the Lipschitz bound. *)
  current_lipschitz_lebesgue_action_family_lipschitz : forall i x y,
    inner_norm (@euclidean_inner_productP R n) (g i x-g i y) <=
      L*inner_norm (@euclidean_inner_productP R m) (x-y);
  (** Source: 4.1.25, p. 383; the
      smooth differentials are bounded by the same L. *)
  current_lipschitz_lebesgue_action_family_differential_bound : forall i x,
    @euclidean_operator_norm R m n
      (@current_map_differential R m n setT (g i) x) <= L;
  (** Source: 4.1.25, p. 383, applying
      the value convergence in 4.1.2, p. 347. *)
  current_lipschitz_lebesgue_action_family_uniform : forall eta:R, 0<eta ->
    exists N:nat, forall i:nat, (N<=i)%N -> forall x,
      inner_norm (@euclidean_inner_productP R n) (g i x-f x)<eta;
  (** Source: 4.1.25, p. 383; the
      differentials converge boundedly almost everywhere. *)
  current_lipschitz_lebesgue_action_family_differential_ae :
    measure_almost_everywhere (@euclidean_lebesgue_measure R m) [set x |
      forall D:Hom (R_n R m) (R_n R n),
        has_norm_differential
          (inner_norm (@euclidean_inner_productP R m))
          (inner_norm (@euclidean_inner_productP R n)) setT f x D ->
        forall eta:R, 0<eta -> exists N:nat, forall i:nat, (N<=i)%N ->
          @euclidean_operator_norm R m n
            (@current_map_differential R m n setT (g i) x-D)<eta]
}.
