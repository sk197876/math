(** Federer (1969), 2.4.12, p. 86: maximal dominated linear graphs yield a
    total linear extension. This private construction follows the book's
    maximality and single-vector interval proof, retaining infinite seminorm
    values. The existing finite-valued proof in DominatedGraphExtension.v
    supplies the graph-order pattern. Source context: ExtendedSeminormUP.v.
    Only the existing set-theoretic maximal principle is used; no
    Hahn–Banach theorem is imported. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp Require Import reals constructive_ereal.
From Federer Require Import ExtendedSeminormUP PartialLinearMap
  LinearGraphAdjoinValue ExtendedSeminormAdjoinInterval ExtendedSeminormAdjoinDomination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Extension.
Variable K : realType.
Variable V : lmodType K.
Local Notation W := K^o.
Variable N : V -> \bar K.
Hypothesis hN : is_extended_seminorm N.
Variable R0 : V -> W -> Prop.
Hypothesis h0 : linear_graph R0.
Hypothesis hdom0 : forall x c, R0 x c -> (c%:E <= N x)%E.

(** Source for [extended_dominated_graph_extension_property]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Specify a linear graph extending the original graph and obeying the given seminorm bound. *)
Definition extended_dominated_graph_extension_property R := linear_graph R /\
  (forall x w, R0 x w -> R x w) /\ (forall x w, R x w -> (w%:E <= N x)%E).
Local Notation T := {R : V -> W -> Prop | extended_dominated_graph_extension_property R}.

(** Source for [extended_dominated_graph_inclusion]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Supporting partial-order law for inclusion of dominated extension graphs. *)
Definition extended_dominated_graph_inclusion (a b : T) := forall x w, sval a x w -> sval b x w.

(** Source for [extended_dominated_graph_inclusion_refl]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Supporting partial-order law for inclusion of dominated extension graphs. *)
Lemma extended_dominated_graph_inclusion_refl (a : T) : extended_dominated_graph_inclusion a a.
Proof. by []. Qed.

(** Source for [extended_dominated_graph_inclusion_trans]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Supporting partial-order law for inclusion of dominated extension graphs. *)
Lemma extended_dominated_graph_inclusion_trans (a b c : T) :
  extended_dominated_graph_inclusion a b -> extended_dominated_graph_inclusion b c -> extended_dominated_graph_inclusion a c.
Proof. by move=> ab bc x w /ab /bc. Qed.

(** Source for [extended_dominated_graph_inclusion_antisym]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Supporting partial-order law for inclusion of dominated extension graphs. *)
Lemma extended_dominated_graph_inclusion_antisym (a b : T) :
  extended_dominated_graph_inclusion a b -> extended_dominated_graph_inclusion b a -> a=b.
Proof.
case: a => a ha; case: b => b hb; move=> hab hba; apply: eq_exist.
apply: funext => x; apply: funext => w; apply: propext; split; [exact: hab|exact: hba].
Qed.

(** Source for [extended_dominated_graph_chain_upper]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    A chain of dominated linear graph extensions has a dominated linear upper bound, given by its union. *)
Lemma extended_dominated_graph_chain_upper (F : set T) : total_on F extended_dominated_graph_inclusion ->
  exists b : T, forall a, F a -> extended_dominated_graph_inclusion a b.
Proof.
move=> hF; have [hn|hn] := pselect (exists a, F a).
- have [a ha] := hn.
  pose R x w := exists b : T, F b /\ sval b x w.
  have hR : linear_graph R.
    split.
    + exists a; split=> //; exact: (proj1 (proj1 (svalP a))).
    split.
    + move=> x y u v [b [hb hbu]] [c [hc hcv]].
      have [hbc|hcb] := hF b c hb hc.
      * exists c; split=> //; exact: (proj1 (proj2 (proj1 (svalP c)))) (hbc _ _ hbu) hcv.
      * exists b; split=> //; exact: (proj1 (proj2 (proj1 (svalP b)))) hbu (hcb _ _ hcv).
    split.
    + move=> d x u [b [hb hbu]]; exists b; split=> //.
      exact: (proj1 (proj2 (proj2 (proj1 (svalP b))))) hbu.
    + move=> x u v [b [hb hbu]] [c [hc hcv]].
      have [hbc|hcb] := hF b c hb hc.
      * exact: (proj2 (proj2 (proj2 (proj1 (svalP c))))) (hbc _ _ hbu) hcv.
      * exact: (proj2 (proj2 (proj2 (proj1 (svalP b))))) hbu (hcb _ _ hcv).
  have hb : forall x w, R0 x w -> R x w.
    move=> x w hx; exists a; split=> //; exact: (proj1 (proj2 (svalP a))) hx.
  have hd : forall x w, R x w -> (w%:E <= N x)%E.
    move=> x w [b [_ hx]]; exact: (proj2 (proj2 (svalP b))) hx.
  exists (exist extended_dominated_graph_extension_property R (conj hR (conj hb hd))) => b hb' x w hx.
  by exists b.
- have hb : extended_dominated_graph_extension_property R0 by split=> //; split.
  exists (exist extended_dominated_graph_extension_property R0 hb) => a ha.
  exfalso; apply: hn; by exists a.
Qed.

(** Source for [extended_dominated_total_linear_graph_extension]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    The maximal dominated graph is total: otherwise the single-vector interval construction would extend it strictly. *)
Theorem extended_dominated_total_linear_graph_extension :
  exists R, extended_dominated_graph_extension_property R /\ forall x, exists w, R x w.
Proof.
pose Rb (a b : T) := `[< extended_dominated_graph_inclusion a b >].
have hchain (F : set T) : total_on F Rb -> exists b : T, forall a, F a -> Rb a b.
  move=> hF; have hF' : total_on F extended_dominated_graph_inclusion.
    by move=> s t hs ht; case: (hF s t hs ht) => /asboolP h; [left|right].
  have [b hb] := extended_dominated_graph_chain_upper hF'.
  by exists b => a ha; apply/asboolP; exact: hb.
have [a ha'] := @Zorn T Rb (fun a => asboolT (@extended_dominated_graph_inclusion_refl a))
  (fun a b c ab bc => asboolT (extended_dominated_graph_inclusion_trans (asboolW ab) (asboolW bc)))
  (fun a b ab ba => extended_dominated_graph_inclusion_antisym (asboolW ab) (asboolW ba)) hchain.
have ha b : extended_dominated_graph_inclusion a b -> b = a by move=> /asboolP /ha'.
exists (sval a); split; first exact: svalP.
move=> x; have [hx|hx] := pselect (exists w, sval a x w); first exact: hx.
have hn w : ~ sval a x w by move=> h; apply: hx; exists w.
have hlin : linear_graph (sval a) := proj1 (svalP a).
have hdom : forall y w, sval a y w -> (w%:E <= N y)%E := proj2 (proj2 (svalP a)).
have [c [hlo hup]] := @extended_seminorm_real_interval_exists K V N hN (sval a) hlin hdom x.
have hR : extended_dominated_graph_extension_property (graph_adjoin_value (sval a) x c).
  split; first exact: graph_adjoin_value_linear hlin hn.
  split.
  - move=> y w hw; apply: graph_adjoin_value_contains; exact: (proj1 (proj2 (svalP a))) hw.
  - exact: (@extended_seminorm_adjoin_graph_dominated K V N hN (sval a) hlin x c hdom hlo hup).
pose b : T := exist extended_dominated_graph_extension_property (graph_adjoin_value (sval a) x c) hR.
have hab : extended_dominated_graph_inclusion a b by move=> y w hy; exact: graph_adjoin_value_contains hy.
have he := ha b hab.
have hb : sval b x c := @graph_adjoin_value_vector K V W (sval a) x c hlin.
rewrite he in hb; exfalso; exact: hn c hb.
Qed.

(** Source for [extended_dominated_extended_graph]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Supporting selection and verification of the maximal dominated linear graph, using the preceding proved existence theorem. *)
Definition extended_dominated_extended_graph := sval (constructive_indefinite_description extended_dominated_total_linear_graph_extension).

(** Source for [extended_dominated_extended_graphP]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Supporting selection and verification of the maximal dominated linear graph, using the preceding proved existence theorem. *)
Lemma extended_dominated_extended_graphP : extended_dominated_graph_extension_property extended_dominated_extended_graph.
Proof. exact: (proj1 (svalP (constructive_indefinite_description extended_dominated_total_linear_graph_extension))). Qed.

(** Source for [extended_dominated_extended_graph_total]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Supporting selection and verification of the maximal dominated linear graph, using the preceding proved existence theorem. *)
Lemma extended_dominated_extended_graph_total x : exists w, extended_dominated_extended_graph x w.
Proof. exact: (proj2 (svalP (constructive_indefinite_description extended_dominated_total_linear_graph_extension))). Qed.

(** Source for [extended_dominated_linear_extension]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Choose the unique scalar paired with each vector in the total dominated graph. *)
Definition extended_dominated_linear_extension x : W := sval (constructive_indefinite_description (extended_dominated_extended_graph_total x)).

(** Source for [extended_dominated_linear_extension_graph]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    Supporting selection and verification of the maximal dominated linear graph, using the preceding proved existence theorem. *)
Lemma extended_dominated_linear_extension_graph x : extended_dominated_extended_graph x (extended_dominated_linear_extension x).
Proof. exact: (svalP (constructive_indefinite_description (extended_dominated_extended_graph_total x))). Qed.

(** Source for [extended_dominated_linear_extension_linear]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    The unique values in the total linear graph form a linear functional. *)
Lemma extended_dominated_linear_extension_linear : linear extended_dominated_linear_extension.
Proof.
move=> c x y; have [hZ [hD [hS hU]]] := proj1 extended_dominated_extended_graphP.
apply: (hU (c *: x+y)); first exact: extended_dominated_linear_extension_graph.
exact: hD _ _ _ _ (hS c _ _ (extended_dominated_linear_extension_graph x)) (extended_dominated_linear_extension_graph y).
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V W *:%R extended_dominated_linear_extension extended_dominated_linear_extension_linear.

(** Source for [extended_dominated_linear_extensionE]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    The resulting functional agrees with every pair in the original graph. *)
Lemma extended_dominated_linear_extensionE x w : R0 x w -> extended_dominated_linear_extension x = w.
Proof.
move=> h; have hu := proj2 (proj2 (proj2 (proj1 extended_dominated_extended_graphP))).
exact: hu x _ _ (extended_dominated_linear_extension_graph x) (proj1 (proj2 extended_dominated_extended_graphP) x w h).
Qed.
(** Source for [extended_dominated_linear_extension_bound]: Federer 2.4.12, p. 86,
    maximal-extension proof of Hahn–Banach. Supporting construction:
    The resulting total linear functional obeys the prescribed extended-valued seminorm bound. *)
Lemma extended_dominated_linear_extension_bound x : ((extended_dominated_linear_extension x)%:E <= N x)%E.
Proof.
apply: (proj2 (proj2 extended_dominated_extended_graphP)).
exact: extended_dominated_linear_extension_graph.
Qed.
End Extension.
