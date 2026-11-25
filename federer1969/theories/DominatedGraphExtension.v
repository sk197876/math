(** Federer (1969), 1.10.5, p. 48: supporting Hahn-Banach extension for norm
    duality and positivity, following 2.4.12, p. 86. This proves the
    finite-valued seminorm case. Zorn's lemma is the existing set-theoretic
    background; the domination and one-vector extension arguments are proved
    within the project. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp Require Import reals.
From Federer Require Import TensorUP Bilinear RealNormUP PartialLinearMap
  LinearGraphAdjoinValue SeminormAdjoinInterval SeminormAdjoinDomination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Extension.
Variable K : realType.
Variable V : lmodType K.
Local Notation W := K^o.
Variable N : V -> K.
Hypothesis hN : is_real_seminorm N.
Variable R0 : V -> W -> Prop.
Hypothesis h0 : linear_graph R0.
Hypothesis hdom0 : forall x c, R0 x c -> c<=N x.

(** Source for [dominated_graph_extension_property]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Specify a linear graph extending the original graph and obeying the given seminorm bound. *)
Definition dominated_graph_extension_property R := linear_graph R /\
  (forall x w, R0 x w -> R x w) /\ (forall x w, R x w -> w<=N x).
Local Notation T := {R : V -> W -> Prop | dominated_graph_extension_property R}.

(** Source for [dominated_graph_inclusion]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Supporting partial-order law for inclusion of dominated extension graphs. *)
Definition dominated_graph_inclusion (a b : T) := forall x w, sval a x w -> sval b x w.

(** Source for [dominated_graph_inclusion_refl]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Supporting partial-order law for inclusion of dominated extension graphs. *)
Lemma dominated_graph_inclusion_refl (a : T) : dominated_graph_inclusion a a.
Proof. by []. Qed.

(** Source for [dominated_graph_inclusion_trans]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Supporting partial-order law for inclusion of dominated extension graphs. *)
Lemma dominated_graph_inclusion_trans (a b c : T) :
  dominated_graph_inclusion a b -> dominated_graph_inclusion b c -> dominated_graph_inclusion a c.
Proof. by move=> ab bc x w /ab /bc. Qed.

(** Source for [dominated_graph_inclusion_antisym]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Supporting partial-order law for inclusion of dominated extension graphs. *)
Lemma dominated_graph_inclusion_antisym (a b : T) :
  dominated_graph_inclusion a b -> dominated_graph_inclusion b a -> a=b.
Proof.
case: a => a ha; case: b => b hb; move=> hab hba; apply: eq_exist.
apply: funext => x; apply: funext => w; apply: propext; split; [exact: hab|exact: hba].
Qed.

(** Source for [dominated_graph_chain_upper]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: A chain of dominated linear graph extensions has a dominated linear upper bound, given by its union. *)
Lemma dominated_graph_chain_upper (F : set T) : total_on F dominated_graph_inclusion ->
  exists b : T, forall a, F a -> dominated_graph_inclusion a b.
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
  have hd : forall x w, R x w -> w<=N x.
    move=> x w [b [_ hx]]; exact: (proj2 (proj2 (svalP b))) hx.
  exists (exist dominated_graph_extension_property R (conj hR (conj hb hd))) => b hb' x w hx.
  by exists b.
- have hb : dominated_graph_extension_property R0 by split=> //; split.
  exists (exist dominated_graph_extension_property R0 hb) => a ha.
  exfalso; apply: hn; by exists a.
Qed.

(** Source for [dominated_total_linear_graph_extension]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: The maximal dominated graph is total: otherwise the single-vector interval construction would extend it strictly. *)
Theorem dominated_total_linear_graph_extension :
  exists R, dominated_graph_extension_property R /\ forall x, exists w, R x w.
Proof.
pose Rb (a b : T) := `[< dominated_graph_inclusion a b >].
have hchain (F : set T) : total_on F Rb -> exists b : T, forall a, F a -> Rb a b.
  move=> hF; have hF' : total_on F dominated_graph_inclusion.
    by move=> s t hs ht; case: (hF s t hs ht) => /asboolP h; [left|right].
  have [b hb] := dominated_graph_chain_upper hF'.
  by exists b => a ha; apply/asboolP; exact: hb.
have [a ha'] := @Zorn T Rb (fun a => asboolT (@dominated_graph_inclusion_refl a))
  (fun a b c ab bc => asboolT (dominated_graph_inclusion_trans (asboolW ab) (asboolW bc)))
  (fun a b ab ba => dominated_graph_inclusion_antisym (asboolW ab) (asboolW ba)) hchain.
have ha b : dominated_graph_inclusion a b -> b = a by move=> /asboolP /ha'.
exists (sval a); split; first exact: svalP.
move=> x; have [hx|hx] := pselect (exists w, sval a x w); first exact: hx.
have hn w : ~ sval a x w by move=> h; apply: hx; exists w.
pose c := seminorm_adjoin_value N (sval a) x.
have hlin : linear_graph (sval a) := proj1 (svalP a).
have hdom : forall y w, sval a y w -> w<=N y := proj2 (proj2 (svalP a)).
have hlo y w : sval a y w -> w-N(y-x)<=c.
  exact: (@seminorm_adjoin_value_lower K V N hN (sval a) hlin hdom x y w).
have hup y w : sval a y w -> c<=N(y+x)-w.
  exact: (@seminorm_adjoin_value_upper K V N hN (sval a) hlin hdom x y w).
have hR : dominated_graph_extension_property (graph_adjoin_value (sval a) x c).
  split; first exact: graph_adjoin_value_linear hlin hn.
  split.
  - move=> y w hw; apply: graph_adjoin_value_contains; exact: (proj1 (proj2 (svalP a))) hw.
  - exact: (@seminorm_adjoin_graph_dominated K V N hN (sval a) hlin x c hdom hlo hup).
pose b : T := exist dominated_graph_extension_property (graph_adjoin_value (sval a) x c) hR.
have hab : dominated_graph_inclusion a b by move=> y w hy; exact: graph_adjoin_value_contains hy.
have he := ha b hab.
have hb : sval b x c := @graph_adjoin_value_vector K V W (sval a) x c hlin.
rewrite he in hb; exfalso; exact: hn c hb.
Qed.

(** Source for [dominated_extended_graph]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Supporting selection and verification of the maximal dominated linear graph, using the preceding proved existence theorem. *)
Definition dominated_extended_graph := sval (constructive_indefinite_description dominated_total_linear_graph_extension).

(** Source for [dominated_extended_graphP]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Supporting selection and verification of the maximal dominated linear graph, using the preceding proved existence theorem. *)
Lemma dominated_extended_graphP : dominated_graph_extension_property dominated_extended_graph.
Proof. exact: (proj1 (svalP (constructive_indefinite_description dominated_total_linear_graph_extension))). Qed.

(** Source for [dominated_extended_graph_total]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Supporting selection and verification of the maximal dominated linear graph, using the preceding proved existence theorem. *)
Lemma dominated_extended_graph_total x : exists w, dominated_extended_graph x w.
Proof. exact: (proj2 (svalP (constructive_indefinite_description dominated_total_linear_graph_extension))). Qed.

(** Source for [dominated_linear_extension]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Choose the unique scalar paired with each vector in the total dominated graph. *)
Definition dominated_linear_extension x : W := sval (constructive_indefinite_description (dominated_extended_graph_total x)).

(** Source for [dominated_linear_extension_graph]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: Supporting selection and verification of the maximal dominated linear graph, using the preceding proved existence theorem. *)
Lemma dominated_linear_extension_graph x : dominated_extended_graph x (dominated_linear_extension x).
Proof. exact: (svalP (constructive_indefinite_description (dominated_extended_graph_total x))). Qed.

(** Source for [dominated_linear_extension_linear]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: The unique values in the total linear graph form a linear functional. *)
Lemma dominated_linear_extension_linear : linear dominated_linear_extension.
Proof.
move=> c x y; have [hZ [hD [hS hU]]] := proj1 dominated_extended_graphP.
apply: (hU (c *: x+y)); first exact: dominated_linear_extension_graph.
exact: hD _ _ _ _ (hS c _ _ (dominated_linear_extension_graph x)) (dominated_linear_extension_graph y).
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V W *:%R dominated_linear_extension dominated_linear_extension_linear.

(** Source for [dominated_linear_extensionE]: Federer 1.10.5, p. 48,
    supporting Hahn-Banach proof from 2.4.12, p. 86.
    In words: The resulting functional agrees with every pair in the original graph. *)
Lemma dominated_linear_extensionE x w : R0 x w -> dominated_linear_extension x = w.
Proof.
move=> h; have hu := proj2 (proj2 (proj2 (proj1 dominated_extended_graphP))).
exact: hu x _ _ (dominated_linear_extension_graph x) (proj1 (proj2 dominated_extended_graphP) x w h).
Qed.
(** Source for [dominated_linear_extension_bound]: Federer 1.10.5,
    p. 48, supporting Hahn-Banach conclusion from 2.4.12, p. 86:
    the resulting total linear functional remains dominated by N. *)
Lemma dominated_linear_extension_bound x : dominated_linear_extension x <= N x.
Proof.
apply: (proj2 (proj2 dominated_extended_graphP)).
exact: dominated_linear_extension_graph.
Qed.
End Extension.
