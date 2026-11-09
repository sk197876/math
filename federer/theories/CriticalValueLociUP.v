(** Federer (1969), 3.4.1, p. 310: independent actual rank-locus and image laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  NormDifferentialUP LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_critical_value_loci]: the actual set
    {x in A:dim im Df(x)<=nu} and its actual image in 3.4.1, p. 310.
    Every differential must be the genuine bounded linear approximation.
    Rank uses an actual finite basis of its range, not a chosen matrix.
    Neither a Hausdorff-nullity conclusion nor target finite dimension
    occurs among these independent defining laws. *)
Record is_critical_value_loci (R:realType) m (Y:lmodType R) (NY:Y->R)
    (A:set (R_n R m)) (f:R_n R m->Y) nu (C:set (R_n R m)) (V:set Y):Prop:={
  (** Source for [critical_rank_locus_equation]: the original rank
      condition of 3.4.1, p. 310, at actual differentiability points
      of the original domain. No value is assigned to Df elsewhere. *)
  critical_rank_locus_equation:forall a,C a <-> A a /\
    exists D:Hom (R_n R m) Y,
      has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY A f a D /\
      exists r,has_linear_rank D r /\(r<=nu)%N;
  (** Source for [critical_value_image_equation]: the original image
      f[{x:dim im Df(x)<=nu}] in 3.4.1, p. 310, with no measurability
      or replacement-by-hull condition. *)
  critical_value_image_equation:V=f @` C
}.
