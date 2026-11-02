(** Federer (1969), 2.7.16, printed pp. 138 and 140, examples (5) and (7):
    "the space X of all m dimensional affine subspaces of R^n". Federer
    gives X no topology. Here an m dimensional affine subspace of V is a set
    tau_a W = {x : x - a in W} with W in G(V, m) (1.6.2, p. 24); these are
    the affine subspaces of 2.7.16, p. 133, whose direction {x - y : x, y in
    S} is m dimensional. Each such S has a direction dir S in G(V, m) and a
    nearest point to 0, the unique point of S perpendicular to dir S, and S
    is the set tau_{nearest S} dir S. The space X carries the initial
    topology of S |-> (dir S, nearest S) into G(V, m) x V, where G(V, m) has
    the topology of W |-> P_W of GrassmannHomogeneousSpace.v; equivalently,
    S is identified with the nearest point retraction x |-> nearest S +
    P_{dir S}(x) of V onto S, a member of A(V, V) (2.7.16, p. 133). X is
    Hausdorff. Every univalent affine map tau_z o g carries X into itself
    (affine_subspace_image, to be used also for the affine group of example
    (5)). The isometry group G of example (7) acts on X by A(g, S) = g[S]; X
    is a homogeneous space of G in the sense of 2.7.1, p. 121, and is
    locally compact. The proof of the openness of the orbit maps uses that
    of the action of O(n) on G(n, m). The function delta(S) = distance(S, 0)
    of p. 140 is |nearest S|; it is continuous. The local erratum has no
    entry for pp. 138–140. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerMetric InnerNormedTopology
  LinearBasis Bilinear TensorUP Hom HomInner ModuleQuotient GrassmannSubspaces OrthogonalMaps
  IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws HomeomorphismUP HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure GrassmannHomogeneousSpace AffineMaps
  AffineGroupTopology IsometryGroupStructure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AffineCosets.
Variable R : realType.
Variable V : lmodType R.
Variable m : nat.

(** Source for [affine_coset]: tau_a W = {x : x - a in W}, the
    translate of a vector subspace W by a, Federer 2.7.16, p. 140
    ("p^{-1}{y} = tau_{p*(y)} ker p"). Definition. *)
Definition affine_coset (a : V) (W : G V m) : set V := [set x | grassmann_val W (x - a)].

(** Source for [affine_coset_add]: a + w belongs to tau_a W for w in W,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_coset_add (a : V) (W : G V m) w : grassmann_val W w -> affine_coset a W (a + w).
Proof. by rewrite /affine_coset /= addrC addKr. Qed.

(** Source for [affine_coset_base]: a belongs to tau_a W, Federer
    2.7.16, p. 140. Supporting lemma. *)
Lemma affine_coset_base (a : V) (W : G V m) : affine_coset a W a.
Proof. by rewrite /affine_coset /= subrr; exact: subspace_zero. Qed.

(** Source for [affine_coset_move]: tau_a W = tau_x W for x in tau_a W,
    Federer 2.7.16, p. 140 ("tau_z ker p = tau_{(p* o p) z} ker p").
    Supporting lemma. *)
Lemma affine_coset_move (a x : V) (W : G V m) : affine_coset a W x -> affine_coset a W = affine_coset x W.
Proof.
rewrite /affine_coset /= => hx; apply/seteqP; split=> y /= hy.
- have -> : y - x = (y - a) - (x - a) by rewrite opprB addrA subrK.
  exact: subspace_sub.
- have -> : y - a = (y - x) + (x - a) by rewrite addrA subrK.
  exact: subspace_add.
Qed.

(** Source for [affine_coset_direction_unique]: the direction of an
    affine subspace is determined, Federer 2.7.16, p. 133: if
    tau_a W = tau_b W', then W = W'. Supporting lemma. *)
Lemma affine_coset_direction_unique (a a' : V) (W W' : G V m) :
  affine_coset a W = affine_coset a' W' -> W = W'.
Proof.
move=> he; have ha : affine_coset a' W' a by rewrite -he; exact: affine_coset_base.
apply: grassmann_ext=> v; split=> hv.
- have h1 : affine_coset a W (a + v) := affine_coset_add a hv.
  rewrite he (affine_coset_move ha) /affine_coset /= in h1.
  by move: h1; rewrite addrC addKr.
- have h1 : affine_coset a' W' (a + v).
    rewrite (affine_coset_move ha) /affine_coset /= addrC addKr; exact: hv.
  by move: h1; rewrite -he /affine_coset /= addrC addKr.
Qed.

(** Source for [affine_coset_is_affine_subspace]: tau_a W is an affine
    subspace in the sense of Federer 2.7.16, p. 133: s v + t w belongs to
    it whenever v, w belong to it and s + t = 1. Supporting lemma. *)
Lemma affine_coset_is_affine_subspace (a : V) (W : G V m) : is_affine_subspace (affine_coset a W).
Proof.
move=> v w s t hv hw hst; rewrite /affine_coset /=.
have -> : s *: v + t *: w - a = s *: (v - a) + t *: (w - a).
  by rewrite !scalerBr addrACA -opprD -scalerDl hst scale1r.
by apply: subspace_add; exact: subspace_scale.
Qed.

End AffineCosets.

Section AffineSubspaceCarrier.
Variable R : realType.
Variable V : lmodType R.
Variable m : nat.

(** Source for [is_affine_subspace_dim]: "m dimensional affine
    subspaces of R^n", Federer 2.7.16, pp. 138 and 140: the sets
    tau_a W with W in G(V, m). Definition. *)
Definition is_affine_subspace_dim (S : set V) : Prop := exists a (W : G V m), S = affine_coset a W.

(** Source for [affine_subspace_carrier]: the set of all m dimensional
    affine subspaces of V, Federer 2.7.16, pp. 138 and 140, as a type
    with a choice structure. Definition. *)
Definition affine_subspace_carrier : Type := {S : set V | is_affine_subspace_dim S}.
HB.instance Definition _ := gen_eqMixin affine_subspace_carrier.
HB.instance Definition _ := gen_choiceMixin affine_subspace_carrier.

(** Source for [affine_points]: the set of points of an m dimensional
    affine subspace, Federer 2.7.16, p. 140. Definition. *)
Definition affine_points (S : affine_subspace_carrier) : set V := proj1_sig S.

(** Source for [affine_subspace_ext]: an affine subspace is determined
    by its points, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_ext (S S' : affine_subspace_carrier) :
  (forall x, affine_points S x <-> affine_points S' x) -> S = S'.
Proof.
case: S S'=> [S hS] [S' hS'] /= h.
have he : S = S' by apply/seteqP; split=> x /h.
subst S'; congr exist; exact: Prop_irrelevance.
Qed.

(** Source for [affine_subspace_of]: the m dimensional affine subspace
    tau_a W, Federer 2.7.16, p. 140. Definition. *)
Definition affine_subspace_of (a : V) (W : G V m) : affine_subspace_carrier :=
  exist _ (affine_coset a W) (ex_intro _ a (ex_intro _ W erefl)).

(** Source for [affine_base]: a point of an m dimensional affine
    subspace, chosen; Federer 2.7.16, p. 140. Definition; later results
    use only affine_subspace_cosetE. *)
Definition affine_base (S : affine_subspace_carrier) : V := projT1 (cid (proj2_sig S)).

(** Source for [affine_direction]: the direction of an m dimensional
    affine subspace S, the member W of G(V, m) with S = tau_a W,
    Federer 2.7.16, pp. 133 and 140. Definition by choice; it is unique
    by affine_coset_direction_unique. *)
Definition affine_direction (S : affine_subspace_carrier) : G V m := projT1 (cid (projT2 (cid (proj2_sig S)))).

(** Source for [affine_subspace_cosetE]: S = tau_a (dir S) for the
    chosen point a, Federer 2.7.16, p. 140. Specification of
    affine_base and affine_direction. *)
Lemma affine_subspace_cosetE (S : affine_subspace_carrier) :
  affine_points S = affine_coset (affine_base S) (affine_direction S).
Proof. exact: (projT2 (cid (projT2 (cid (proj2_sig S))))). Qed.

(** Source for [affine_points_coset]: S = tau_x (dir S) for every point
    x of S, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_points_coset (S : affine_subspace_carrier) x :
  affine_points S x -> affine_points S = affine_coset x (affine_direction S).
Proof. by rewrite affine_subspace_cosetE=> hx; exact: affine_coset_move. Qed.

(** Source for [affine_points_diff]: for a point x of S, y belongs to S
    if and only if y - x belongs to dir S, Federer 2.7.16, p. 133.
    Supporting lemma. *)
Lemma affine_points_diff (S : affine_subspace_carrier) x y :
  affine_points S x -> (affine_points S y <-> grassmann_val (affine_direction S) (y - x)).
Proof. by move=> hx; rewrite (affine_points_coset hx). Qed.

(** Source for [affine_subspace_of_points]: the points of tau_a W,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_of_points (a : V) (W : G V m) : affine_points (affine_subspace_of a W) = affine_coset a W.
Proof. by []. Qed.

(** Source for [affine_subspace_of_direction]: dir (tau_a W) = W,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_of_direction (a : V) (W : G V m) : affine_direction (affine_subspace_of a W) = W.
Proof.
apply: esym; apply: (@affine_coset_direction_unique R V m a (affine_base (affine_subspace_of a W))).
by rewrite -affine_subspace_cosetE.
Qed.

(** Source for [affine_subspace_eq_point]: two m dimensional affine
    subspaces with the same direction and a common point are equal,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_eq_point (S S' : affine_subspace_carrier) x :
  affine_direction S = affine_direction S' -> affine_points S x -> affine_points S' x -> S = S'.
Proof.
move=> hd hx hx'; apply: affine_subspace_ext=> y.
by rewrite (affine_points_coset hx) (affine_points_coset hx') hd.
Qed.

(** Source for [affine_subspace_eta]: S = tau_x (dir S) for every point
    x of S, as points of X, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_eta (S : affine_subspace_carrier) x :
  affine_points S x -> S = affine_subspace_of x (affine_direction S).
Proof.
move=> hx; apply: (affine_subspace_eq_point (x := x))=> //.
- by rewrite affine_subspace_of_direction.
- exact: affine_coset_base.
Qed.

End AffineSubspaceCarrier.

Arguments affine_subspace_carrier {R} V m.
Arguments affine_subspace_of {R V m} a W.
Arguments affine_points {R V m} S x.
Arguments affine_direction {R V m} S.
Arguments affine_base {R V m} S.

Section NearestPoint.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variable m : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.
Local Notation X := (affine_subspace_carrier V m).
Local Notation P W := (grassmann_projection hC hB hc W).
Local Notation N := (inner_norm hB).

(** Source for [affine_nearest]: the point of S nearest to 0, x - P(x)
    for any point x of S with P the orthogonal projection onto dir S,
    Federer 2.7.16, p. 140 ("delta(W) = distance(W, 0)"; 1.7.4, p. 30).
    Definition; later results use only its characterisation. *)
Definition affine_nearest (S : X) : V := affine_base S - P (affine_direction S) (affine_base S).

(** Source for [affine_nearest_eq]: nearest S = x - P_{dir S}(x) for
    every point x of S, Federer 1.7.4, p. 30. Supporting lemma. *)
Lemma affine_nearest_eq (S : X) x : affine_points S x -> affine_nearest S = x - P (affine_direction S) x.
Proof.
move=> hx; rewrite /affine_nearest.
set a := affine_base S; set L := affine_direction S.
have hd : grassmann_val L (x - a) by move: hx; rewrite affine_subspace_cosetE.
have hP : P L (x - a) = x - a := grassmann_projection_fixed hC hB hc hd.
have hl : P L (x - a) = P L x - P L a := linearB (hom_as_linear (P L)) x a.
have hPx : P L x = P L a + (x - a) by rewrite -hP hl addrC subrK.
by rewrite hPx opprD opprB addrCA [x + _]addrC subrK addrC.
Qed.

(** Source for [affine_nearest_mem]: the nearest point belongs to S,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_nearest_mem (S : X) : affine_points S (affine_nearest S).
Proof.
rewrite affine_subspace_cosetE /affine_coset /= /affine_nearest addrC addKr.
apply: subspace_opp; exact: (grassmann_projectionP hC hB hc _).1.
Qed.

(** Source for [affine_nearest_perp]: the nearest point is perpendicular
    to dir S, Federer 1.7.4, p. 30. Supporting lemma. *)
Lemma affine_nearest_perp (S : X) w : grassmann_val (affine_direction S) w -> B (affine_nearest S) w = 0.
Proof. by move=> hw; rewrite /affine_nearest; exact: (grassmann_projectionP hC hB hc _).2. Qed.

(** Source for [affine_nearest_unique]: a point of S perpendicular to
    dir S is the nearest point, Federer 1.7.4, p. 30. Supporting lemma. *)
Lemma affine_nearest_unique (S : X) x :
  affine_points S x -> (forall w, grassmann_val (affine_direction S) w -> B x w = 0) -> x = affine_nearest S.
Proof.
move=> hx hp; have hd : grassmann_val (affine_direction S) (x - affine_nearest S).
  exact: (affine_points_diff x (affine_nearest_mem S)).1 hx.
apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: (grassmann_perpendicular_member_zero hB hd)=> w hw.
by rewrite (bilBl (inner_bilinear hB)) hp // affine_nearest_perp // subrr.
Qed.

(** Source for [affine_subspace_of_nearest]: nearest (tau_a W) =
    a - P_W(a), Federer 1.7.4, p. 30. Supporting lemma. *)
Lemma affine_subspace_of_nearest (a : V) (W : G V m) :
  affine_nearest (affine_subspace_of a W) = a - P W a.
Proof.
rewrite (affine_nearest_eq (x := a)); last exact: affine_coset_base.
by rewrite affine_subspace_of_direction.
Qed.

(** Source for [affine_subspace_nearest_eta]: S = tau_{nearest S} dir S,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_nearest_eta (S : X) : S = affine_subspace_of (affine_nearest S) (affine_direction S).
Proof. exact: affine_subspace_eta (affine_nearest_mem S). Qed.

(** Source for [affine_subspace_pair_injective]: S is determined by
    (dir S, nearest S), Federer 2.7.16, p. 140; supporting the Hausdorff
    property of X. Supporting lemma. *)
Lemma affine_subspace_pair_injective (S S' : X) :
  affine_direction S = affine_direction S' -> affine_nearest S = affine_nearest S' -> S = S'.
Proof. by move=> hd hn; rewrite (affine_subspace_nearest_eta S) (affine_subspace_nearest_eta S') hd hn. Qed.

(** Source for [affine_origin_distance]: delta(S) = distance(S, 0),
    Federer 2.7.16, p. 140, as |nearest S|; its characterisation as the
    least norm of a point of S is affine_origin_distance_least and
    affine_origin_distance_attained. Definition. *)
Definition affine_origin_distance (S : X) : R := N (affine_nearest S).

(** Source for [affine_origin_distance_least]: delta(S) <= |x| for
    every point x of S, Federer 2.7.16, p. 140: x = nearest S + w with
    w in dir S perpendicular to nearest S. Supporting lemma. *)
Lemma affine_origin_distance_least (S : X) x : affine_points S x -> affine_origin_distance S <= N x.
Proof.
move=> hx; pose a := affine_nearest S; pose w := x - a.
have hw : grassmann_val (affine_direction S) w := (affine_points_diff x (affine_nearest_mem S)).1 hx.
have hxw : x = a + w by rewrite /w addrC subrK.
have hsq : N x ^+ 2 = N a ^+ 2 + N w ^+ 2.
  rewrite !(inner_norm_sqr hB) hxw (inner_sum_square hB) (affine_nearest_perp hw) addr0 addr0.
  by [].
rewrite /affine_origin_distance -/a.
have h0 := inner_norm_nonnegative hB a; have h1 := inner_norm_nonnegative hB x.
have h2 : 0 <= N w ^+ 2 by exact: sqr_ge0.
rewrite -(ler_pXn2r (n := 2)) ?nnegrE //; lra.
Qed.

(** Source for [affine_origin_distance_attained]: delta(S) is attained
    at the nearest point, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_origin_distance_attained (S : X) :
  exists2 x, affine_points S x & N x = affine_origin_distance S.
Proof. by exists (affine_nearest S); [exact: affine_nearest_mem|]. Qed.

End NearestPoint.

Arguments affine_nearest {R U V C B} hC hB {m c} hc S.
Arguments affine_origin_distance {R U V C B} hC hB {m c} hc S.

Section AffineSubspaceTopology.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GR := (grassmann_space hC hB hc hb).
Local Notation XC := (affine_subspace_carrier V m).
Local Notation P W := (grassmann_projection hC hB hc W).
Local Notation nearest := (affine_nearest hC hB hc).

(** Source for [affine_subspace_space]: "the space X of all m
    dimensional affine subspaces of R^n", Federer 2.7.16, pp. 138 and
    140, as a topological space: the initial topology of
    S |-> (dir S, nearest S) into G(V, m) x V. Definition; this topology
    is supplied, see the header. *)
Definition affine_subspace_space :=
  initial_topology (fun S : XC => ((affine_direction S : GR), (nearest S : VT))).

(** Source for [affine_subspace_pair_continuous]: S |-> (dir S,
    nearest S) is continuous on X, by definition of the topology,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_pair_continuous :
  continuous (fun S : affine_subspace_space => ((affine_direction S : GR), (nearest S : VT))).
Proof. exact: initial_continuous. Qed.

(** Source for [affine_direction_continuous]: S |-> dir S is continuous
    from X to G(V, m), Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_direction_continuous : continuous (fun S : affine_subspace_space => (affine_direction S : GR)).
Proof.
move=> S; apply: (@continuous_comp affine_subspace_space (GR * VT)%type GR
  (fun S : affine_subspace_space => ((affine_direction S : GR), (nearest S : VT))) fst).
  exact: affine_subspace_pair_continuous.
exact: first_projection_continuous.
Qed.

(** Source for [affine_nearest_continuous]: S |-> nearest S is
    continuous from X to V, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_nearest_continuous : continuous (fun S : affine_subspace_space => (nearest S : VT)).
Proof.
move=> S; apply: (@continuous_comp affine_subspace_space (GR * VT)%type VT
  (fun S : affine_subspace_space => ((affine_direction S : GR), (nearest S : VT))) snd).
  exact: affine_subspace_pair_continuous.
exact: second_projection_continuous.
Qed.

(** Source for [affine_projection_continuous]: S |-> P_{dir S} is
    continuous from X to Hom(V, V), Federer 2.7.16, p. 140. Supporting
    lemma. *)
Lemma affine_projection_continuous :
  continuous (fun S : affine_subspace_space => (P (affine_direction S) : HVV)).
Proof.
move=> S; apply: (@continuous_comp affine_subspace_space GR HVV
  (fun S : affine_subspace_space => (affine_direction S : GR)) (fun W : GR => (P W : HVV))).
  exact: affine_direction_continuous.
exact: grassmann_space_projection_continuous.
Qed.

(** Source for [affine_subspace_continuous_into]: a map f into X is
    continuous when S |-> dir f(t) and t |-> nearest f(t) are continuous,
    by definition of the topology of X, Federer 2.7.16, p. 140.
    Supporting lemma. *)
Lemma affine_subspace_continuous_into (T : topologicalType) (f : T -> affine_subspace_space) :
  continuous (fun t => (affine_direction (f t) : GR)) -> continuous (fun t => (nearest (f t) : VT)) ->
  continuous f.
Proof.
move=> hd hn; apply: continuous_comp_initial.
exact: (@topological_pair_continuous T GR VT _ _ hd hn).
Qed.

(** Source for [affine_subspace_space_hausdorff]: X is a Hausdorff
    space, Federer 2.7.1, p. 121, and 2.7.16, p. 140: S |-> (dir S,
    nearest S) is univalent and G(V, m) x V is Hausdorff. Supporting
    lemma. *)
Lemma affine_subspace_space_hausdorff : hausdorff_space affine_subspace_space.
Proof.
move=> S S' hcl.
have hH : hausdorff_space (GR * VT)%type.
  apply: product_hausdorff; first exact: grassmann_space_hausdorff.
  exact: inner_space_hausdorff.
have he : ((affine_direction S : GR), (nearest S : VT)) = ((affine_direction S' : GR), (nearest S' : VT)).
  apply: hH=> A A' hA hA'.
  have hcont := affine_subspace_pair_continuous.
  have [w [hwA hwA']] := hcl _ _ (hcont S A hA) (hcont S' A' hA').
  by exists ((affine_direction w : GR), (nearest w : VT)).
by case: he=> h1 h2; exact: affine_subspace_pair_injective h1 h2.
Qed.

(** Source for [affine_origin_distance_continuous]: "delta is
    continuous", Federer 2.7.16, p. 141: delta(S) = |nearest S|.
    Direct formalisation. *)
Theorem affine_origin_distance_continuous :
  continuous (fun S : affine_subspace_space => (affine_origin_distance hC hB hc S : R)).
Proof.
move=> S; apply: (@continuous_comp affine_subspace_space VT R (fun S => (nearest S : VT)) Num.norm).
  exact: affine_nearest_continuous.
exact: norm_continuous.
Qed.

End AffineSubspaceTopology.

Arguments affine_subspace_space {R U V C B} hC hB {m c n b} hc hb.

Section AffineImages.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation VT := (inner_metric_space hB).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation AG := (GL * VT)%type.
Local Notation XC := (affine_subspace_carrier V m).
Local Notation amap := (affine_group_map hB hb).

(** Source for [affine_linear_injective]: the linear part g of
    tau_z o g in the affine group is univalent, Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma affine_linear_injective (p : AG) : injective (hom_as_linear (set_val p.1 : Hom V V)).
Proof. exact: (set_valP p.1). Qed.

(** Source for [affine_subspace_image]: the image f[S] of an m
    dimensional affine subspace S under a univalent affine map
    f = tau_z o g, an m dimensional affine subspace with direction g[dir S],
    Federer 2.7.16, pp. 138 and 140 (the actions of the affine group and
    of the isometry group on X). Definition. *)
Definition affine_subspace_image (p : AG) (S : XC) : XC :=
  affine_subspace_of (amap p (affine_base S))
    (grassmann_image hC hB hc (@affine_linear_injective p) (affine_direction S)).

(** Source for [affine_subspace_imageE]: x belongs to f[S] if and only
    if x = f(w) for some w in S, Federer 2.7.16, p. 140. Supporting
    lemma. *)
Lemma affine_subspace_imageE (p : AG) (S : XC) x :
  affine_points (affine_subspace_image p S) x <-> exists2 w, affine_points S w & amap p w = x.
Proof.
pose g : Hom V V := set_val p.1.
have hl (u w : V) : g (u + w) = g u + g w := linearD (hom_as_linear g) u w.
have hs (u w : V) : g (u - w) = g u - g w := linearB (hom_as_linear g) u w.
rewrite affine_subspace_of_points /affine_coset /=; split.
- move=> [l hl' hgl]; exists (affine_base S + l).
    by rewrite affine_subspace_cosetE; exact: affine_coset_add.
  rewrite /amap /affine_group_map -/g hl addrA hgl.
  by rewrite /affine_group_map addrC subrK.
- move=> [w hw <-]; exists (w - affine_base S).
    by move: hw; rewrite affine_subspace_cosetE.
  by rewrite -/g hs /amap /affine_group_map -/g opprD addrACA subrr add0r addrC.
Qed.

(** Source for [affine_subspace_image_mem]: f(w) belongs to f[S] for w
    in S, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_image_mem (p : AG) (S : XC) w :
  affine_points S w -> affine_points (affine_subspace_image p S) (amap p w).
Proof. by move=> hw; apply/affine_subspace_imageE; exists w. Qed.

(** Source for [affine_subspace_image_direction]: dir f[S] = g[dir S]
    for f = tau_z o g, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_image_direction (p : AG) (S : XC) :
  affine_direction (affine_subspace_image p S) =
    grassmann_image hC hB hc (@affine_linear_injective p) (affine_direction S).
Proof. exact: affine_subspace_of_direction. Qed.

(** Source for [affine_subspace_image_mul]: (f o h)[S] = f[h[S]],
    Federer 2.7.1, p. 121, for the actions of 2.7.16, pp. 138 and 140.
    Supporting lemma. *)
Lemma affine_subspace_image_mul (p q : AG) (S : XC) :
  affine_subspace_image (affine_group_mul hB hb p q) S = affine_subspace_image p (affine_subspace_image q S).
Proof.
apply: affine_subspace_ext=> x; rewrite !affine_subspace_imageE; split.
- move=> [w hw <-]; exists (amap q w); first exact: affine_subspace_image_mem.
  by rewrite affine_group_map_mul.
- move=> [w' /affine_subspace_imageE [w hw <-] <-]; exists w=> //.
  by rewrite affine_group_map_mul.
Qed.

(** Source for [affine_subspace_image_unit]: 1_V[S] = S, Federer 2.7.1,
    p. 121. Supporting lemma. *)
Lemma affine_subspace_image_unit (S : XC) : affine_subspace_image (affine_group_unit hB hb) S = S.
Proof.
apply: affine_subspace_ext=> x; rewrite affine_subspace_imageE affine_group_map_unit; split.
- by move=> [w hw <-].
- by move=> hx; exists x.
Qed.

End AffineImages.

Arguments affine_subspace_image {R U V C B} hC hB {m c n b} hc hb p S.

Section IsometryAction.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GR := (grassmann_space hC hB hc hb).
Local Notation X := (affine_subspace_space hC hB hc hb).
Local Notation P W := (grassmann_projection hC hB hc W).
Local Notation nearest := (affine_nearest hC hB hc).
Local Notation O := (orthogonal_group hB hb).
Local Notation G := (isometry_group hB hb).
Local Notation om := (@orthogonal_element_map R V B hB n b hb).
Local Notation gact := (grassmann_action hC hB hc hb).

(** Source for [affine_subspace_action]: the action A(g, S) = g[S] of
    the isometry group G on the space X of m dimensional affine
    subspaces, Federer 2.7.16, p. 140. Definition. *)
Definition affine_subspace_action (g : G) (S : X) : X :=
  affine_subspace_image hC hB hc hb (set_val g) S.

(** Source for [affine_subspace_actionE]: x belongs to g[S] if and only
    if x = g(w) for some w in S, Federer 2.7.16, p. 140. Supporting
    lemma. *)
Lemma affine_subspace_actionE (g : G) (S : X) x :
  affine_points (affine_subspace_action g S) x <-> exists2 w, affine_points S w & isometry_map g w = x.
Proof. exact: affine_subspace_imageE. Qed.

(** Source for [affine_subspace_action_mem]: g(w) belongs to g[S] for w
    in S, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_action_mem (g : G) (S : X) w :
  affine_points S w -> affine_points (affine_subspace_action g S) (isometry_map g w).
Proof. exact: affine_subspace_image_mem. Qed.

(** Source for [affine_subspace_action_direction]: dir g[S] = L(g)[dir S],
    Federer 2.7.16, p. 140, the action of O(n) on G(n, m) of example (6).
    Supporting lemma. *)
Lemma affine_subspace_action_direction (g : G) (S : X) :
  affine_direction (affine_subspace_action g S) = gact (isometry_linear g) (affine_direction S).
Proof.
rewrite /affine_subspace_action affine_subspace_image_direction.
by apply: grassmann_ext=> y; split=> hy; exact: hy.
Qed.

(** Source for [affine_subspace_action_nearest]: nearest g[S] =
    y - P(y) with y = g(nearest S) and P the projection onto dir g[S],
    Federer 1.7.4, p. 30, and 2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_action_nearest (g : G) (S : X) :
  nearest (affine_subspace_action g S) =
    isometry_map g (nearest S) - P (affine_direction (affine_subspace_action g S)) (isometry_map g (nearest S)).
Proof. by apply: affine_nearest_eq; apply: affine_subspace_action_mem; exact: affine_nearest_mem. Qed.

Variables (mulS : G -> G -> G) (invS : G -> G) (eS : G).
Hypothesis hS : is_subgroup_restriction (affine_group_mul hB hb) (affine_group_inv hB hb)
  (affine_group_unit hB hb) G mulS invS eS.
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) O mulO invO eO.

(** Source for [affine_subspace_action_continuous]: the action of G on X
    is continuous, Federer 2.7.1, p. 121, and 2.7.16, p. 140: dir g[S] =
    L(g)[dir S] depends continuously on (g, S) by example (6), and
    nearest g[S] = y - P(y) with y = g(nearest S). Supporting lemma. *)
Lemma affine_subspace_action_continuous : continuous (fun q : G * X => affine_subspace_action q.1 q.2).
Proof.
have hGa := homogeneous_action_continuous (grassmann_space_homogeneous hC hc hO).
have hdir : continuous (fun q : G * X => (affine_direction (affine_subspace_action q.1 q.2) : GR)).
  have -> : (fun q : G * X => (affine_direction (affine_subspace_action q.1 q.2) : GR)) =
      (fun r : O * GR => gact r.1 r.2) \o (fun q : G * X => (isometry_linear q.1, (affine_direction q.2 : GR))).
    by apply: funext=> q; rewrite /= affine_subspace_action_direction.
  move=> q; apply: (@continuous_comp (G * X)%type (O * GR)%type GR
    (fun q : G * X => (isometry_linear q.1, (affine_direction q.2 : GR))) (fun r : O * GR => gact r.1 r.2));
    last exact: hGa.
  apply: (@topological_pair_continuous (G * X)%type O GR).
    move=> r; apply: (@continuous_comp (G * X)%type G O (@fst G X) isometry_linear r).
      exact: first_projection_continuous.
    exact: isometry_linear_continuous.
  move=> r; apply: (@continuous_comp (G * X)%type X GR (@snd G X) (fun S : X => (affine_direction S : GR)) r).
    exact: second_projection_continuous.
  exact: affine_direction_continuous.
have hy : continuous (fun q : G * X => (isometry_map q.1 (nearest q.2) : VT)).
  move=> q; apply: (@continuous_comp (G * X)%type (G * VT)%type VT
    (fun q : G * X => (q.1, (nearest q.2 : VT))) (fun r : G * VT => (isometry_map r.1 r.2 : VT))).
    apply: (@topological_pair_continuous (G * X)%type G VT); first exact: first_projection_continuous.
    move=> r; apply: (@continuous_comp (G * X)%type X VT (@snd G X) (fun S : X => (nearest S : VT)) r).
      exact: second_projection_continuous.
    exact: affine_nearest_continuous.
  exact: isometry_map_continuous.
apply: affine_subspace_continuous_into=> //.
have hP : continuous (fun q : G * X => (P (affine_direction (affine_subspace_action q.1 q.2)) : HVV)).
  move=> q; apply: (continuous_comp (hdir q)); exact: grassmann_space_projection_continuous.
have hPy := hom_evaluation_continuous_comp hP hy.
have -> : (fun q : G * X => (nearest (affine_subspace_action q.1 q.2) : VT)) =
    (fun q : G * X => (isometry_map q.1 (nearest q.2) : VT)) -
      (fun q : G * X => ((P (affine_direction (affine_subspace_action q.1 q.2)) : Hom V V)
        (isometry_map q.1 (nearest q.2)) : VT)).
  by apply: funext=> q; rewrite affine_subspace_action_nearest.
by move=> q; apply: continuousB; [exact: hy|exact: hPy].
Qed.

(** Source for [affine_subspace_action_compatible]: A(gh, S) =
    A(g, A(h, S)), Federer 2.7.1, p. 121, for the action of G on X,
    2.7.16, p. 140. Supporting lemma. *)
Lemma affine_subspace_action_compatible (g h : G) (S : X) :
  affine_subspace_action (mulS g h) S = affine_subspace_action g (affine_subspace_action h S).
Proof. by rewrite /affine_subspace_action (subgroup_restriction_mul hS) affine_subspace_image_mul. Qed.

(** Source for [affine_subspace_action_transitive]: G acts transitively
    on X, Federer 2.7.16, p. 140. Proof supplied: choose t in O(n) with
    t[dir S_1] = dir S_2 (example (6)); then tau_z o t with
    z = nearest S_2 - t(nearest S_1) maps S_1 onto S_2. *)
Lemma affine_subspace_action_transitive (S1 S2 : X) : exists g, affine_subspace_action g S1 = S2.
Proof.
have [t ht] := grassmann_action_transitive (affine_direction S1 : GR) (affine_direction S2 : GR).
exists (isometry_of t (nearest S2 - om t (nearest S1))).
apply: (affine_subspace_eq_point (x := nearest S2)); last exact: affine_nearest_mem.
  by rewrite affine_subspace_action_direction isometry_of_linear.
have := affine_subspace_action_mem (isometry_of t (nearest S2 - om t (nearest S1))) (affine_nearest_mem hC hB hc S1).
by rewrite isometry_of_mapE subrK.
Qed.

(** Source for [affine_subspace_orbit_open]: "for each x in X the map
    A^x ... is open", Federer 2.7.1, p. 121, for the action of G on X,
    2.7.16, p. 140. Proof supplied. Let tau_{z_0} o t_0 lie in U, choose
    neighbourhoods A_1 of t_0 and C_1 of z_0 with
    {tau_z o t : t in A_1, z in C_1} contained in U, let a = nearest S,
    W_0 = (tau_{z_0} o t_0)[S] and d = z_0 + t_0(a) - nearest W_0, a
    vector of dir W_0. The map zeta(t, W) = nearest W - t(a) + P_{dir W}(d)
    is continuous with zeta(t_0, W_0) = z_0. If dir W = t[dir S] with t
    near t_0 (the orbit maps of O(n) on G(n, m) are open) and W is near
    W_0, then z = zeta(t, W) lies in C_1 and (tau_z o t)[S] = W, since
    both have direction t[dir S] and contain nearest W + P_{dir W}(d). *)
Lemma affine_subspace_orbit_open (S : X) : is_open_map (orbit_map affine_subspace_action S).
Proof.
have hGr := grassmann_space_homogeneous hC hc hO.
move=> Uo hUo; rewrite openE=> W0 [g0 hg0 <-]; rewrite /interior.
pose a : V := nearest S; pose L : GR := affine_direction S.
pose t0 := isometry_linear g0; pose z0 : VT := isometry_translation g0.
pose W1 := affine_subspace_action g0 S.
pose F := fun q : O * VT => isometry_of q.1 q.2.
have hU' : open (F @^-1` Uo) by apply: open_comp hUo=> q _; exact: isometry_of_continuous.
have hFU : (F @^-1` Uo) (t0, z0) by rewrite /F /= isometry_ofK.
have [[A1 C1] [hA1 hC1] hAC] : nbhs (t0, z0) (F @^-1` Uo) by apply: open_nbhs_nbhs; split.
pose d : V := isometry_map g0 a - nearest W1.
have hd : grassmann_val (affine_direction W1) d.
  apply/(affine_points_diff (isometry_map g0 a) (affine_nearest_mem hC hB hc W1)).
  exact: affine_subspace_action_mem (affine_nearest_mem hC hB hc S).
pose zeta := fun q : O * X => (nearest q.2 : VT) - (om q.1 a : VT) + ((P (affine_direction q.2) : Hom V V) d : VT).
have hzeta : continuous zeta.
  have h1 : continuous (fun q : O * X => (nearest q.2 : VT)).
    move=> q; apply: (@continuous_comp (O * X)%type X VT (@snd O X) (fun S : X => (nearest S : VT)) q).
      exact: second_projection_continuous.
    exact: affine_nearest_continuous.
  have h2 : continuous (fun q : O * X => (om q.1 a : VT)).
    apply: (@hom_evaluation_continuous_comp R V B hB n b hb (O * X)%type (fun q : O * X => (om q.1 : HVV))
      (fun _ => (a : VT))); last exact: cst_continuous.
    move=> q; apply: (@continuous_comp (O * X)%type O HVV (@fst O X) (fun g : O => (om g : HVV)) q).
      exact: first_projection_continuous.
    exact: orthogonal_element_continuous.
  have h3 : continuous (fun q : O * X => ((P (affine_direction q.2) : Hom V V) d : VT)).
    apply: (@hom_evaluation_continuous_comp R V B hB n b hb (O * X)%type
      (fun q : O * X => (P (affine_direction q.2) : HVV)) (fun _ => (d : VT))); last exact: cst_continuous.
    move=> q; apply: (@continuous_comp (O * X)%type X HVV (@snd O X)
      (fun S : X => (P (affine_direction S) : HVV)) q).
      exact: second_projection_continuous.
    exact: affine_projection_continuous.
  have -> : zeta = ((fun q : O * X => (nearest q.2 : VT)) - (fun q : O * X => (om q.1 a : VT))) +
      (fun q : O * X => ((P (affine_direction q.2) : Hom V V) d : VT)) by apply: funext.
  move=> q; apply: continuousD; last exact: h3.
  by apply: continuousB; [exact: h1|exact: h2].
have hz0 : zeta (t0, W1) = z0.
  rewrite /zeta /= (grassmann_projection_fixed hC hB hc hd) /d /isometry_map -/t0 -/z0.
  by rewrite addrCA (addrAC (nearest W1)) subrr add0r addrK.
have hpre : nbhs (t0, W1) (zeta @^-1` C1) by apply: hzeta; rewrite hz0.
have [[A2 N2] [hA2 hN2] hAN] := hpre.
pose Oint := (A1 `&` A2)°.
have hOint : open Oint := @open_interior _ _.
have ht0 : Oint t0 by rewrite /Oint /interior /=; exact: filterI.
have hOL := homogeneous_orbit_open hGr L hOint.
have hdirW1 : (affine_direction W1 : GR) = gact t0 L by exact: affine_subspace_action_direction.
have hN : nbhs W1 ((fun W : X => (affine_direction W : GR)) @^-1` (orbit_map gact L @` Oint)).
  apply: affine_direction_continuous; apply: open_nbhs_nbhs; split=> //.
  by rewrite hdirW1; exists t0.
apply: (@filterS _ _ (nbhs_filter _) _ _ _ (filterI hN2 hN))=> W [hW2 [t htO htL]].
have htA := interior_subset htO; have [htA1 htA2] := htA.
have hzC : C1 (zeta (t, W)) by exact: hAN (t, W) (conj htA2 hW2).
have hFU' : Uo (F (t, zeta (t, W))) by exact: hAC (t, zeta (t, W)) (conj htA1 hzC).
exists (F (t, zeta (t, W)))=> //.
rewrite /orbit_map; apply: (affine_subspace_eq_point (x := nearest W + (P (affine_direction W) : Hom V V) d)).
- by rewrite affine_subspace_action_direction /F isometry_of_linear -htL.
- have := affine_subspace_action_mem (F (t, zeta (t, W))) (affine_nearest_mem hC hB hc S).
  by rewrite /F isometry_of_mapE /zeta /= addrAC subrK.
- apply/(affine_points_diff _ (affine_nearest_mem hC hB hc W)); rewrite addrC addKr.
  exact: (grassmann_projectionP hC hB hc _).1.
Qed.

(** Source for [affine_subspace_homogeneous]: the space X of m
    dimensional affine subspaces of V is a homogeneous space of the
    isometry group G through A(g, S) = g[S], Federer 2.7.16, p. 140, in
    the sense of 2.7.1, p. 121. Direct formalisation; Federer leaves the
    topology and the verification to the reader. *)
Theorem affine_subspace_homogeneous : is_homogeneous_space mulS affine_subspace_action.
Proof.
split.
- exact: affine_subspace_action_continuous.
- exact: affine_subspace_action_compatible.
- exact: affine_subspace_orbit_open.
- move=> S; apply/seteqP; split=> // S' _.
  have [g hg] := affine_subspace_action_transitive S S'.
  by exists g.
Qed.

(** Source for [affine_subspace_space_locally_compact]: X is locally
    compact, the standing hypothesis of Federer 2.7.1, p. 121, for
    2.7.16, p. 140. Supporting lemma: the image of a compact
    neighbourhood K of g under the open continuous orbit map A^S is a
    compact neighbourhood of g[S], closed since X is Hausdorff. *)
Lemma affine_subspace_space_locally_compact : locally_compact [set: X].
Proof.
have hA := affine_subspace_homogeneous.
have hl := lch_group_locally_compact (isometry_group_lch hS).
move=> S _.
pose g0 := eS.
have hS0 : orbit_map affine_subspace_action S g0 = S.
  rewrite /orbit_map /g0 /affine_subspace_action (subgroup_restriction_unit hS).
  exact: affine_subspace_image_unit.
have [K hK [hKc _]] := hl g0 I; rewrite withinET in hK.
have hpK : compact (orbit_map affine_subspace_action S @` K).
  apply: continuous_compact=> //; apply: continuous_subspaceT; exact: orbit_map_continuous hA S.
exists (orbit_map affine_subspace_action S @` K); last first.
  split=> //; apply: compact_closed hpK; exact: affine_subspace_space_hausdorff.
rewrite withinET nbhsE; exists (orbit_map affine_subspace_action S @` K°).
  split; first exact: (homogeneous_orbit_open hA S (@open_interior _ K)).
  by exists g0=> //.
by move=> _ [k hk <-]; exists k=> //; exact: interior_subset.
Qed.

End IsometryAction.

Arguments affine_subspace_action {R U V C B} hC hB {m c n b} hc hb g S.
