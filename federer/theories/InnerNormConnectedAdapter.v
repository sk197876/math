(** General topology supporting Federer (1969), 3.1.24,
    p. 240: connectedness is unchanged by using the
    inner-product metric or the metric of its norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness NormMetric
  InnerNormTopologyAdapters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [inner_norm_connectedP]: the connected-domain
    argument in Federer 3.1.24, p. 240, uses the
    same topology in the metric and differential interfaces.
    Transfer the relatively open and relatively closed sets
    in the definition of connectedness using the proved
    open-set and closed-set equivalences. *)
Lemma inner_norm_connectedP (R:realType) (X:lmodType R) (B:X->X->R)
    (hB:is_inner_product B) (A:set X) :
  @connected (inner_metric_space hB) A <->
  @connected (real_norm_metric_space (inner_norm_real_norm hB)) A.
Proof.
split.
- move=>hc S hn [U hU hSU] [V hV hSV].
  have ho:exists2 C:set (inner_metric_space hB),open C & S=A `&` C.
    exists U; last exact hSU; exact ((inner_norm_openP hB U).2 hU).
  have hcl:exists2 C:set (inner_metric_space hB),closed C & S=A `&` C.
    exists V; last exact hSV; exact ((inner_norm_closedP hB V).2 hV).
  exact (hc S hn ho hcl).
- move=>hc S hn [U hU hSU] [V hV hSV].
  have ho:exists2 C:set (real_norm_metric_space (inner_norm_real_norm hB)),open C & S=A `&` C.
    exists U; last exact hSU; exact ((inner_norm_openP hB U).1 hU).
  have hcl:exists2 C:set (real_norm_metric_space (inner_norm_real_norm hB)),closed C & S=A `&` C.
    exists V; last exact hSV; exact ((inner_norm_closedP hB V).1 hV).
  exact (hc S hn ho hcl).
Qed.
