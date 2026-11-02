(** Federer (1969), 3.2.28(2), printed p. 265:
    Q inverse Q(g) is the isometric image of SO(m)
    under R_g(u)=g u, including its Hausdorff measure
    in every natural degree. The later half-volume law
    requires m positive; this fibre identity does not. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric OrthogonalMaps
  AdjointCriteria EuclideanRectangularAdjoint EuclideanHomInnerCharts
  EuclideanStiefelInnerSplitting EuclideanExteriorWordSmooth
  EuclideanExteriorFrameFibres HausdorffMeasure HausdorffIsometricEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_exterior_frame_fibre_measure]: the
    fibre-measure identity immediately before the coarea
    formula in Federer 3.2.28(2), p. 265. Its value
    is the actual Hausdorff measure of SO(m), without
    assuming either its finiteness or a volume formula. *)
Theorem euclidean_exterior_frame_fibre_measure (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->forall k,
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R m n)) k
    [set h|is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R n) (hom_as_linear h) /\
      euclidean_exterior_word_map h=euclidean_exterior_word_map g]=
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R m m)) k
    (@euclidean_special_orthogonal_set R m).
Proof.
move=>hg k.
pose X:=inner_metric_space (@euclidean_hom_inner_productP R m m).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R m n).
pose f:=fun u:X=>(hom_comp g u:Y).
pose p:=fun h:Y=>(hom_comp (euclidean_rectangular_adjoint g) h:X).
have hCan:cancel g (euclidean_rectangular_adjoint g).
  exact:(orthogonal_iff_adjoint_left_inverse (@euclidean_inner_productP R m)
    (euclidean_rectangular_adjoint_pairing g)).1 hg.
have hfp:cancel f p.
  move=>u; apply:hom_ext=>x; exact:hCan.
have hDist u v:mdist (f u) (f v)=mdist u v.
  rewrite !inner_metric_distanceE.
  have hSub:(hom_comp g u-hom_comp g v)%R=hom_comp g (u-v)%R.
    apply:hom_ext=>x; change (g (u x)-g (v x)=g (u x-v x)).
    by rewrite linearB.
  change (inner_norm (@euclidean_hom_inner_productP R m n)
    (hom_comp g u-hom_comp g v)=inner_norm (@euclidean_hom_inner_productP R m m) (u-v)).
  rewrite hSub; exact:(@euclidean_stiefel_vertical_norm_isometry R m n g hg (u-v)).
have hImage:f @` (@euclidean_special_orthogonal_set R m)=
    [set h:Y|is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R n) (hom_as_linear h) /\
      euclidean_exterior_word_map h=euclidean_exterior_word_map g].
  apply/seteqP; split=>h.
  - move=>[u hu <-]; have hgu:is_orthogonal_map (@euclidean_inner_product R m)
        (@euclidean_inner_product R n) (hom_as_linear (hom_comp g u)).
      move=>x y.
      change (euclidean_inner_product (g (u x)) (g (u y))=euclidean_inner_product x y).
      rewrite hg; exact:hu.1.
    split; first exact hgu.
    apply:(euclidean_exterior_frame_fibre_special_orthogonal hg hgu).2.
    exists u; by split.
  - move=>[hh hQ].
    have [u [hu hgu]]:=(euclidean_exterior_frame_fibre_special_orthogonal hg hh).1 hQ.
    exists u; first exact hu.
    exact:esym hgu.
rewrite -hImage; exact:hausdorff_isometric_embedding_invariance hfp hDist k _.
Qed.
