(** Federer (1969), 3.4.1, p. 310: existence and uniqueness of the original critical sets. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  NormDifferentialUP LinearRankUP CriticalValueLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_value_loci_exists]: the displayed original
    sets of 3.4.1, p. 310, exist by separation and image formation.
    This construction serves only to prove the independent laws; the
    public sets are subsequently opaque. *)
Theorem critical_value_loci_exists (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) nu:
  exists C V,is_critical_value_loci NY A f nu C V.
Proof.
pose C:= [set a|A a /\exists D:Hom (R_n R m) Y,
  has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY A f a D /\
  exists r,has_linear_rank D r /\(r<=nu)%N].
exists C,(f @` C);constructor;by [].
Qed.

(** Source for [critical_value_loci_unique]: the exact original
    membership and image equations of 3.4.1, p. 310, determine both
    sets uniquely. No auxiliary differential or image basis is selected. *)
Theorem critical_value_loci_unique (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) nu C V C' V':
  is_critical_value_loci NY A f nu C V ->is_critical_value_loci NY A f nu C' V' ->
  C=C' /\V=V'.
Proof.
move=>h h'.
have hC:C=C'.
  apply/seteqP;split=>a ha.
  - exact:((critical_rank_locus_equation h' a).2 ((critical_rank_locus_equation h a).1 ha)).
  - exact:((critical_rank_locus_equation h a).2 ((critical_rank_locus_equation h' a).1 ha)).
split;first exact:hC.
by rewrite (critical_value_image_equation h) (critical_value_image_equation h') hC.
Qed.
