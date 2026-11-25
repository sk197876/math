(** Federer (1969), 3.2.31, pp. 268–269: supporting
    countable class-one representatives of a Lipschitz map, by
    3.1.16, p. 228. This expands the measurability reduction
    before the printed small linear-rescaling argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormRegularity EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_class_one_agreement_cover]: independent laws
    for a supporting reduction in Federer 3.2.31, pp. 268–269.
    Countably many global class-one maps agree with the original
    map on closed sets whose union contains Lebesgue almost
    every source point. This auxiliary route uses 3.1.16 before
    the printed rescaling, rather than asserting measurability
    of sets with unrestricted derivative-remainder quantifiers. *)
Record is_class_one_agreement_cover (R:realType) m n
    (F:R_n R m.+1->R_n R n) (G:nat->R_n R m.+1->R_n R n)
    (C:nat->set (R_n R m.+1)):Prop:={
  (** Source for [class_one_agreement_cover_class]: actual
      class-one approximants of 3.1.16, p. 228, supporting
      the local derivative estimates in 3.2.31, p. 269. *)
  class_one_agreement_cover_class:forall j,
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R m.+1))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT (G j) 1;
  (** Source for [class_one_agreement_cover_closed]: closed
      equality sets of the continuous original map and its
      approximants, supporting 3.2.31, p. 269. *)
  class_one_agreement_cover_closed:forall j,
    @closed [the topologicalType of inner_metric_space (@euclidean_inner_productP R m.+1)] (C j);
  (** Source for [class_one_agreement_cover_equal]: exact
      value agreement, supporting the fibre identifications
      in Federer 3.2.31, p. 269. *)
  class_one_agreement_cover_equal:forall j x,C j x ->F x=G j x;
  (** Source for [class_one_agreement_cover_conull]: countably
      many decreasing approximation errors give a conull union,
      supporting Federer 3.2.31, pp. 268–269. *)
  class_one_agreement_cover_conull:
    @euclidean_lebesgue_measure R m.+1 (~` \bigcup_j C j)=0%E
}.
