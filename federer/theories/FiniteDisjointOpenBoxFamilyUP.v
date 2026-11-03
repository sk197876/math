(** Federer (1969), 3.2.41, printed p. 277, second proof
    paragraph: finite disjoint subfamilies of the proper open-box
    family F. Indexing retains actual box endpoints and sets. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanOpenCoordinateBoxUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_finite_disjoint_open_box_family]: direct finite
    disjoint family in Federer 3.2.41, p. 277. Only the original
    box membership and pairwise disjointness are specified. Measure,
    cut, separation and Brunn--Minkowski conclusions are not laws. *)
Record is_finite_disjoint_open_box_family (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))):Prop:={
  (** Source for [finite_disjoint_open_box_law]: direct membership
      of each member in F in Federer 3.2.41, p. 277. *)
  finite_disjoint_open_box_law:forall i,is_euclidean_open_coordinate_box (a i) (b i) (G i);
  (** Source for [finite_disjoint_open_box_disjoint_law]: direct
      disjointness of the finite original family in Federer
      3.2.41, p. 277, before any splitting or summation. *)
  finite_disjoint_open_box_disjoint_law:forall i j,i!=j ->forall x,G i x ->G j x ->False
}.
