(** Federer (1969), 2.6.6, pp. 120–121: compactness supplies compatible
    families and controls their coordinate images. This supporting proof
    allows non-surjective bonding maps. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot finmap boolp classical_sets topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP
  InverseCompatibilityFinite CompactClosedFamilyMeeting NormalizedProductSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [inverse_family_meets_closed_coordinate]: compact
    finite-intersection argument supporting the inverse-limit
    extension in Federer 2.6.6, pp. 120–121. If every upper
    coordinate can project into a closed set, some fully compatible
    family has its prescribed coordinate in that set. *)
Theorem inverse_family_meets_closed_coordinate (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (u0 : prod_topology Y) (i0 : I) (K : set (Y i0)) :
  is_compact_inverse_system le b -> closed K ->
  (forall k, le i0 k -> exists y : Y k, K (b i0 k y)) ->
  exists u : prod_topology Y, compatible_inverse_family le b u /\ K (u i0).
Proof.
move=> hs hK hupper.
pose P := (fun u : prod_topology Y=>u i0) @^-1` K.
have hP : closed P := (@continuous_closedP (prod_topology Y) (Y i0) (fun u=>u i0)).1 (@proj_continuous I Y i0) K hK.
have hcP : compact P.
  exact: subclosed_compact hP
    (compact_factor_product_compact (compact_inverse_system_compact hs)) (@subsetT _ P).
have hfin : forall F : {fset I * I}, exists u : prod_topology Y,
    P u /\ forall ij, ij \in F -> inverse_compatibility_constraint le b ij u.
  move=> F.
  have [k [h0 hk]] := inverse_finite_constraints_upper (compact_inverse_system_directed hs) i0 F.
  have [y hy] := hupper k h0.
  exists (inverse_upper_coordinate_family le b u0 y); split.
  - change (K (inverse_upper_coordinate_family le b u0 y i0)).
    by rewrite (@inverse_upper_coordinate_family_evaluation I le Y b u0 k y i0 h0).
  - move=> [i j] hij; exact (@inverse_upper_family_compatible_pair I le Y b hs u0 k y i j (hk _ hij).1 (hk _ hij).2).
have [u [hu hC]] := @compact_closed_family_meeting (prod_topology Y) [the choiceType of (I*I)%type]
  P (inverse_compatibility_constraint le b) hcP (inverse_compatibility_constraint_closed hs) hfin.
exists u; split=> // i j hij; exact: hC (i,j) hij.
Qed.

(** Source for [compact_inverse_family_exists]: nonemptiness
    of the compact inverse limit, supporting Federer 2.6.6,
    pp. 120–121. The supplied product point is justified by
    normalization when applying this to integral functionals. *)
Theorem compact_inverse_family_exists (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i) (u0 : prod_topology Y) :
  is_compact_inverse_system le b -> exists u, compatible_inverse_family le b u.
Proof.
move=> hs; have [i0 _] := directed_preorder_nonempty (compact_inverse_system_directed hs).
have hup : forall k, le i0 k -> exists y : Y k, (@setT (Y i0)) (b i0 k y).
  by move=> k hk; exists (u0 k).
have [u [hu _]] := inverse_family_meets_closed_coordinate u0 hs (@closedT (Y i0)) hup.
by exists u.
Qed.

(** Source for [inverse_limit_projection_neighborhood]: supporting
    finite-coordinate control of a compact inverse limit, Federer
    2.6.6, pp. 120–121. An open neighborhood of its i-th
    projection contains an entire later bonding-map image. This
    replaces a surjectivity assumption on the bonding maps. *)
Theorem inverse_limit_projection_neighborhood (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i) (u0 : prod_topology Y)
    (i : I) (U : set (Y i)) :
  is_compact_inverse_system le b -> is_compact_inverse_limit le b p ->
  open U -> (forall x, U (p i x)) -> exists j, le i j /\ forall y : Y j, U (b i j y).
Proof.
move=> hs hlim hU hp; apply: contrapT=> hnone.
have hbad : forall k, le i k -> exists y : Y k, (~` U) (b i k y).
  move=> k hk; apply: contrapT=> hn; apply: hnone; exists k; split=> // y.
  apply: contrapT=> hy; apply: hn; by exists y.
have [u [hu hUi]] := inverse_family_meets_closed_coordinate u0 hs (open_closedC hU) hbad.
have [x hx] := compact_inverse_limit_realizes_family hlim hu.
apply: hUi; rewrite -(hx i); exact: hp.
Qed.
