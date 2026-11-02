(** Federer (1969), 2.6.5, pp. 119–120: the usual identifications of finite
    Cartesian products with Euclidean spaces. These supporting topology
    lemmas use the actual coordinate space R_n and its dot-product topology
    from 1.7.1, p. 28. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  CoordinateProjection InnerMetric InnerNormedTopology InnerCoordinateContinuity
  InnerFiniteSynthesis OrthonormalFamilies LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_family_continuous]: supporting
    universal property of product topology for Federer 2.6.5,
    p. 120. General topology background: a family map is
    continuous when all its coordinate maps are continuous. *)
Lemma coordinate_family_continuous (X : topologicalType) (I : eqType)
    (Y : I -> topologicalType) (f : forall i, X -> Y i) :
  (forall i, continuous (f i)) -> continuous (fun x => fun i => f i x).
Proof.
move=> hf x; apply/cvg_sup=> i.
move: x; apply/(@continuousP _ (initial_topology (@^~ i)))=> A [B hB <-].
apply: open_comp hB=> y _; exact: hf.
Qed.

(** Source for [euclidean_coordinate_continuous]: supporting
    continuity of coordinate projections in Federer 2.6.5,
    p. 120, from the dot product in 1.7.1, p. 28. *)
Lemma euclidean_coordinate_continuous (R : realType) n (i : 'I_n) :
  continuous (fun x : inner_metric_space (@euclidean_inner_productP R n) => (x i : R^o)).
Proof.
have he : (fun x : inner_metric_space (@euclidean_inner_productP R n) => (x i : R^o)) =
    (fun x => inner_coordinate (@euclidean_inner_productP R n) (@coordinate_basis R n i) x).
  by apply: funext=> x; rewrite inner_coordinateE euclidean_inner_basis.
rewrite he; exact: inner_coordinate_continuous.
Qed.

(** Source for [euclidean_coordinate_expansion]: supporting
    reconstruction from Cartesian coordinates in Federer
    2.6.5, p. 120, using the orthonormal basis of
    the Euclidean example in 1.7.1, p. 28. *)
Lemma euclidean_coordinate_expansion (R : realType) n (x : R_n R n) :
  \sum_i x i *: (@coordinate_basis R n i) = x.
Proof.
have ho : orthonormal_family (@euclidean_inner_product R n) (@coordinate_basis R n).
  by move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have h := @inner_finite_synthesis_coordinates R (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n) ho x.
rewrite /inner_finite_synthesis in h.
rewrite -[RHS]h; apply: eq_bigr=> i _.
by rewrite inner_coordinateE euclidean_inner_basis.
Qed.

(** Source for [euclidean_map_continuous]: supporting
    coordinate criterion for Euclidean maps in Federer
    2.6.5, p. 120. The topology is the previously
    constructed Euclidean norm topology, not a replacement
    topology chosen for the measure construction. *)
Lemma euclidean_map_continuous (R : realType) (X : topologicalType) n
    (f : X -> inner_metric_space (@euclidean_inner_productP R n)) :
  (forall i, continuous (fun x => (f x i : R^o))) -> continuous f.
Proof.
move=> hf.
have he : f = (fun x => inner_finite_synthesis (@euclidean_inner_productP R n)
  (@coordinate_basis R n) (fun i => f x i)).
  apply: funext=> x; symmetry; exact: euclidean_coordinate_expansion.
rewrite he=> x.
apply: (@continuous_comp X (Topological.clone ('I_n -> R^o) _)
  (Topological.clone (inner_metric_space (@euclidean_inner_productP R n)) _)
  (fun x => fun i => f x i) (inner_finite_synthesis (@euclidean_inner_productP R n)
    (@coordinate_basis R n)) x).
- exact (@coordinate_family_continuous X (Equality.clone 'I_n _)
    (fun _ => Topological.clone R^o _) (fun i x => f x i) hf x).
- exact: inner_finite_synthesis_continuous.
Qed.
