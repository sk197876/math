(** Federer (1969), 2.6.5, pp. 119–120: the first Euclidean factor is
    identified with the scalar line carrying L^1. This supporting
    homeomorphism preserves the existing dot-product topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNormedTopology EuclideanCoordinateTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [euclidean_one_embed]: supporting scalar
    identification of the first Cartesian factor in Federer
    2.6.5, pp. 119–120. *)
Definition euclidean_one_embed (R : realType) (t : R) :
  inner_metric_space (@euclidean_inner_productP R 1) := [ffun _ => t].

(** Source for [euclidean_one_project]: supporting inverse
    identification in Federer 2.6.5, pp. 119–120. *)
Definition euclidean_one_project (R : realType)
    (x : inner_metric_space (@euclidean_inner_productP R 1)) : R := x ord0.

(** Source for [euclidean_one_embedK]: inverse identity for
    the first factor of Federer 2.6.5, pp. 119–120. *)
Lemma euclidean_one_embedK (R : realType) :
  cancel (@euclidean_one_embed R) (@euclidean_one_project R).
Proof. by move=> t; rewrite /euclidean_one_project /euclidean_one_embed ffunE. Qed.

(** Source for [euclidean_one_projectK]: inverse identity
    for the first factor of Federer 2.6.5, pp. 119–120. *)
Lemma euclidean_one_projectK (R : realType) :
  cancel (@euclidean_one_project R) (@euclidean_one_embed R).
Proof.
move=> x; apply/ffunP=> i; rewrite /euclidean_one_embed /euclidean_one_project ffunE.
by rewrite (ord1 i).
Qed.

(** Source for [euclidean_one_embed_continuous]: supporting
    homeomorphism property for Federer 2.6.5, pp. 119–120. *)
Lemma euclidean_one_embed_continuous (R : realType) : continuous (@euclidean_one_embed R).
Proof.
apply: euclidean_map_continuous=> i.
have he : (fun t : R => euclidean_one_embed t i) = (fun t => t).
  by apply: funext=> t; rewrite /euclidean_one_embed ffunE.
rewrite he=> t; exact: cvg_id.
Qed.

(** Source for [euclidean_one_project_continuous]: supporting
    inverse homeomorphism property for Federer 2.6.5,
    pp. 119–120. *)
Lemma euclidean_one_project_continuous (R : realType) : continuous (@euclidean_one_project R).
Proof. exact: (@euclidean_coordinate_continuous R 1 ord0). Qed.
