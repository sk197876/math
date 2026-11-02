(** Federer (1969), 3.2.28(2), printed p. 264:
    the image of Q is exactly the simple unit m-vectors,
    the Euclidean realization of the oriented Grassmannian.
    Positive m is explicit: the literal empty word does
    not supply two orientations in degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanLinearMaps CoordinateProjection
  InnerNorm InnerMetric InnerNormedTopology InnerExteriorPositivity
  OrthogonalMaps OrthonormalFamilies OrthonormalFrameMap
  ExteriorGrading ExteriorNorm ExteriorMaps ExteriorOperatorEstimate FiniteExteriorPowers
  SimpleElementary AssociatedSubspace SimpleVectorFrames
  EuclideanStiefelInnerSplitting EuclideanExteriorWordSmooth EuclideanExteriorWordEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_exterior_word_frame_unit]: Q takes
    orthogonal frames to simple unit exterior vectors, Federer
    3.2.28(2), p. 264, by 1.6.2 and 1.7.5,
    pp. 24 and 32. This inclusion also holds in degree zero. *)
Lemma euclidean_exterior_word_frame_unit (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  simple (euclidean_exterior_word_map g) /\
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (euclidean_exterior_word_map g)= 1.
Proof.
move=>hg; rewrite euclidean_exterior_word_mapE exterior_map_indexed_product.
split; first exact:product_simple.
apply:orthonormal_product_unit_norm=>i j; rewrite hg.
exact:(@euclidean_coordinate_orthonormal_family R m i j).
Qed.

(** Source for [euclidean_exterior_word_image_simple_unit]:
    the exact image identification of Go(n,m) in Federer
    3.2.28(2), p. 264. Orthonormal factorization proves
    the reverse inclusion for every positive degree, without
    an assumed surjectivity or a selected global frame. *)
Theorem euclidean_exterior_word_image_simple_unit (R:realType) m n:
  (0<m)%N ->
  (@euclidean_exterior_word_map R m n) @`
    [set g|is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R n) (hom_as_linear g)]=
  [set x|simple x /\ exterior_norm (euclidean_two_nonzero R)
    (@euclidean_inner_productP R n) x= 1].
Proof.
move=>hm; apply/seteqP; split=>x.
- move=>[g hg <-]; exact:euclidean_exterior_word_frame_unit hg.
- move=>[hs hx].
  pose E:=inner_metric_space
    (exterior_inner_productP (euclidean_two_nonzero R) (@euclidean_inner_productP R n) m).
  have hxN:`|(x:E)|= 1 by rewrite inner_norm_topologyE.
  have [e [he hxe]]:=@unit_simple_frame R (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m hm x hxN hs.
  have [f [hf hfe]]:=orthonormal_frame_map_exists (@euclidean_inner_productP R n) he.
  exists (hom_of_linear f); first exact hf.
  rewrite euclidean_exterior_word_mapE exterior_map_indexed_product.
  have heq:(fun i=>hom_of_linear f (@coordinate_basis R m i))=e.
    apply:funext=>i; exact:hfe.
  by rewrite heq.
Qed.
