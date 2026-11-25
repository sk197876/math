(** General topology supporting Federer (1969), 2.2.10, pp. 65–66:
    first-coordinate projections and maps (x,n) to (f(x),n) are continuous
    in the product topology. These are background lemmas, not additional
    book assertions. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [first_projection_continuous]: supporting continuity
    of p(x,n)=x in Federer 2.2.10, pp. 65–66, for arbitrary
    topological product factors. *)
Lemma first_projection_continuous (X Y : topologicalType) : continuous (@fst X Y).
Proof. move=> p; exact: cvg_fst. Qed.

(** Source for [second_projection_continuous]: supporting second-
    coordinate continuity for the closed graph and inverse-image
    constructions in Federer 2.2.10, pp. 65–66. *)
Lemma second_projection_continuous (X Y : topologicalType) : continuous (@snd X Y).
Proof. move=> p; exact: cvg_snd. Qed.

(** Source for [topological_pair_continuous]: supporting product
    continuity for Federer 2.2.10, pp. 65–66: a pair of
    continuous maps into the factors is continuous into their product. *)
Lemma topological_pair_continuous (X Y Z : topologicalType) (f : X -> Y) (g : X -> Z) :
  continuous f -> continuous g -> continuous (fun x => (f x,g x)).
Proof. move=> hf hg x; exact: cvg_pair (hf x) (hg x). Qed.

(** Source for [first_factor_map_continuous]: supporting map
    (x,n) to (f(x),n) in the inverse-image argument of Federer
    2.2.10, p. 66, first paragraph. *)
Lemma first_factor_map_continuous (X Y Z : topologicalType) (f : X -> Y) :
  continuous f -> continuous (fun p : X * Z => (f p.1,p.2)).
Proof.
move=> hf; apply: topological_pair_continuous.
- move=> p; exact: continuous_comp (@first_projection_continuous X Z p) (hf p.1).
- exact: second_projection_continuous.
Qed.
