(** General finite-dimensional topology supporting
    Federer (1969), 3.3.4, p. 290:
    the actual active inclusion and its
    adjoint projection are continuous. Use
    finite Hom evaluation from 1.7.1, p. 28. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom HomInner GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric HomSpaceTopology TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_rectangular_map_continuous]:
    every actual linear map between these
    finite Euclidean spaces is continuous,
    by 1.7.1, p. 28, supporting the
    active projection and subgroup parameters
    in Federer 3.3.4, p. 290. *)
Theorem euclidean_rectangular_map_continuous (R:realType) d n
    (w:Hom (R_n R d) (R_n R n)):
  continuous (fun u:inner_metric_space (@euclidean_inner_productP R d)=>
    (w u:inner_metric_space (@euclidean_inner_productP R n))).
Proof.
pose U:=inner_metric_space (@euclidean_inner_productP R d).
pose V:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=inner_metric_space (hom_inner_productP (@euclidean_inner_productP R d)
  (@euclidean_inner_productP R n) (@coordinate_basisP R d)).
have hPair:continuous (fun u:U=>(w,u):H*U).
  apply:topological_pair_continuous; first exact:cst_continuous.
  by move=>u; exact:cvg_id.
move=>u; exact:(continuous_comp (hPair u)
  (@hom_evaluation_continuous R (R_n R d) (R_n R n)
    (@euclidean_inner_product R d) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R d) (@euclidean_inner_productP R n)
    d (@coordinate_basis R d) (@coordinate_basisP R d) (w,u))).
Qed.
