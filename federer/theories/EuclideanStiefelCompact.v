(** Federer (1969), 3.2.28(2)–(3), pp. 265–266:
    the area/coarea applications use the compact Stiefel
    manifolds. Compactness follows from the proved transitive
    orthogonal action of 2.7.16, p. 139, in the actual
    Hilbert Hom metric. It is not used to justify openness. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerMetric HomInner OrthogonalMaps OrthogonalGroupTopology
  OrthogonalInjectionSpaces EuclideanHomInnerCharts InnerMetricLawCompatibility HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_stiefel_compact]: compactness of
    O(n,m) from 2.7.16, p. 139, as needed in
    Federer 3.2.28, pp. 265–266. This is the
    actual ambient subset, including empty and zero cases. *)
Theorem euclidean_stiefel_compact (R:realType) m n:
  @compact [the topologicalType of inner_metric_space (@euclidean_hom_inner_productP R m n)]
    [set g|is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R n) (hom_as_linear g)].
Proof.
pose hBm:=@euclidean_inner_productP R m.
pose hBn:=@euclidean_inner_productP R n.
pose hCan:=hom_inner_productP hBm hBn (@coordinate_basisP R m).
pose X:=inner_metric_space hCan.
pose S:set X:=[set g|is_orthogonal_map (@euclidean_inner_product R m)
  (@euclidean_inner_product R n) (hom_as_linear g)].
have [mul [inv [e hO]]]:=orthogonal_group_restriction_exists hBn (@coordinate_basisP R n).
have hC:=@orthogonal_injections_compact R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n) hBm hBn
  m (@coordinate_basis R m) n (@coordinate_basis R n)
  (@coordinate_basisP R m) (@coordinate_basisP R n) mul inv e hO.
have hImage:(@set_val X S) @` setT=S.
  apply/seteqP; split=>x.
  - by move=>[y _ <-]; exact:set_valP y.
  - move=>hx; exists (exist _ x (mem_set hx)); reflexivity.
have hCS:compact S.
  have hV:continuous (@set_val X S) by exact:initial_continuous.
  rewrite -hImage; exact:continuous_compact (continuous_subspaceT hV) hC.
have hIdentity:compact ((fun x:X=>(x:inner_metric_space (@euclidean_hom_inner_productP R m n))) @` S).
  apply:continuous_compact _ hCS.
  exact:continuous_subspaceT (homeomorphism_continuous
    (inner_metric_law_homeomorphism hCan (@euclidean_hom_inner_productP R m n))).
by rewrite image_id in hIdentity.
Qed.
