(** Supporting the rotation parameters in Federer (1969), 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Parts 6–7, pp. 247–250. A family of linear
    maps between fixed Euclidean spaces is continuous in Hom when its values
    on the coordinate basis are continuous. This finite-dimensional topology
    consequence of 1.7.1, p. 28, is proved by the rank-one expansion already
    used for 2.7.16, p. 134. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerNormedTopology Hom HomInner HomSpaceTopology EuclideanCoordinateTopology CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [euclidean_linear_family_continuous]: supporting
    finite-dimensional Hom topology for 2.10.46, p. 204;
    Freilich (1950), Part 7, pp. 249–250. The
    continuity criterion follows from a finite rank-one sum;
    no new topology or external analysis theorem is imported. *)
Theorem euclidean_linear_family_continuous (R : realType) n m (S : topologicalType)
    (h : S -> {linear R_n R n -> R_n R m}) :
  (forall i : 'I_n, continuous (fun s : S=>
    (h s (@coordinate_basis R n i) : inner_metric_space (@euclidean_inner_productP R m)))) ->
  continuous (fun s : S=>(hom_of_linear (h s) : inner_metric_space
    (hom_inner_productP (@euclidean_inner_productP R n)
      (@euclidean_inner_productP R m) (@coordinate_basisP R n)))).
Proof.
move=> hh.
pose H := inner_metric_space (hom_inner_productP (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R m) (@coordinate_basisP R n)).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
have he : (fun s : S=>(hom_of_linear (h s) : H))=
    (fun s=>\sum_(i : 'I_n) (@hom_rank_one R (R_n R n) (R_n R m)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
      (@coordinate_basis R n i) (h s (@coordinate_basis R n i)) : H)).
  apply: funext=> s; apply: hom_ext=> x.
  have hsum (F : 'I_n -> H) : ((\sum_i F i : H) : Hom (R_n R n) (R_n R m)) x=
      \sum_i (F i : Hom (R_n R n) (R_n R m)) x.
    elim/big_rec2: _=> [//|i y G _ <-]; by rewrite hom_addE.
  rewrite hsum.
  change (h s x = \sum_(i : 'I_n)
    (@hom_rank_one R (R_n R n) (R_n R m)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
      (@coordinate_basis R n i) (h s (@coordinate_basis R n i))) x).
  rewrite -{1}(euclidean_coordinate_expansion x) linear_sum.
  apply: eq_bigr=> i _; by rewrite linearZ hom_rank_oneE euclidean_inner_basis.
rewrite he; apply: continuous_big; first exact: add_continuous.
move=> i _ s; exact (continuous_comp (hh i s)
  (@hom_rank_one_continuous R (R_n R n) (R_n R m)
    (@euclidean_inner_product R n) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
    n (@coordinate_basis R n) (@coordinate_basisP R n)
    (@coordinate_basis R n i) (h s (@coordinate_basis R n i)))).
Qed.
