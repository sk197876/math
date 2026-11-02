(** Private existence proof for Federer (1969), 2.10.43, printed p. 201.
    Order nonexpanding partial graphs containing the original graph by
    inclusion. Chain unions give upper bounds; the general set-theoretic
    Zorn principle gives a maximal graph; the proved one-point lemma makes
    its domain the entire source. The resulting map will be hidden by the
    later opaque interface. Only general set-theoretic maximality is
    imported; no external extension theorem is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP
  NonexpandingGraph KirszbraunGraphOnePoint KirszbraunExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Extension.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Variable S : set X.
Variable f : X -> Y.
Hypothesis hSf : is_metric_lipschitz_bound S f 1.

(** Source for [original_nonexpanding_graph]: direct graph
    of the original map on its exact source in
    the class Omega of 2.10.43, p. 201. *)
Definition original_nonexpanding_graph (x : X) (y : Y) := S x /\ f x=y.

(** Source for [original_nonexpanding_graph_laws]: supporting
    initial element of Omega in 2.10.43, p. 201,
    obtained from the original bound one. *)
Lemma original_nonexpanding_graph_laws : is_metric_nonexpanding_graph original_nonexpanding_graph.
Proof.
move=> x y u v [hx <-] [hy <-].
have hh := hSf.2 x y hx hy; by rewrite mul1r in hh.
Qed.

(** Source for [nonexpanding_graph_extension_property]: supporting
    graph specification of the partial extensions in
    Omega of 2.10.43, p. 201. Containment of
    the original graph and nonexpansion are the only laws. *)
Definition nonexpanding_graph_extension_property (G : X -> Y -> Prop) :=
  (forall x y, original_nonexpanding_graph x y -> G x y) /\ is_metric_nonexpanding_graph G.
Local Notation T := {G : X -> Y -> Prop | nonexpanding_graph_extension_property G}.

(** Source for [nonexpanding_graph_extension_inclusion]: direct
    inclusion order on the partial graph extensions
    in 2.10.43, p. 201. *)
Definition nonexpanding_graph_extension_inclusion (a b : T) :=
  forall x y, sval a x y -> sval b x y.

(** Source for [nonexpanding_graph_extension_refl]: supporting
    reflexivity for the maximality argument of
    2.10.43, p. 201. *)
Lemma nonexpanding_graph_extension_refl (a : T) : nonexpanding_graph_extension_inclusion a a.
Proof. by []. Qed.

(** Source for [nonexpanding_graph_extension_trans]: supporting
    transitivity for the maximality argument of
    2.10.43, p. 201. *)
Lemma nonexpanding_graph_extension_trans (a b c : T) :
  nonexpanding_graph_extension_inclusion a b -> nonexpanding_graph_extension_inclusion b c ->
  nonexpanding_graph_extension_inclusion a c.
Proof. by move=> hab hbc x y /hab /hbc. Qed.

(** Source for [nonexpanding_graph_extension_antisym]: supporting
    antisymmetry of graph inclusion in 2.10.43,
    p. 201, by functional and propositional extensionality. *)
Lemma nonexpanding_graph_extension_antisym (a b : T) :
  nonexpanding_graph_extension_inclusion a b -> nonexpanding_graph_extension_inclusion b a -> a=b.
Proof.
case: a=> a ha; case: b=> b hb; move=> hab hba; apply: eq_exist.
apply: funext=> x; apply: funext=> y; apply: propext; split; [exact: hab|exact: hba].
Qed.

(** Source for [nonexpanding_graph_chain_upper]: direct chain-union upper
    bound for 2.10.43, p. 201 Two graph pairs lie together in a larger chain
    member, preserving the distance law. The empty chain uses the original
    graph. *)
Lemma nonexpanding_graph_chain_upper (F : set T) :
  total_on F nonexpanding_graph_extension_inclusion ->
  exists b : T, forall a, F a -> nonexpanding_graph_extension_inclusion a b.
Proof.
move=> hchain; case: (pselect (F !=set0))=> [[a ha]|hempty].
- pose G x y := exists b : T, F b /\ sval b x y.
  have hG : nonexpanding_graph_extension_property G.
    split.
    - move=> x y hxy; exists a; split=> //; exact: (svalP a).1 x y hxy.
    - move=> x y u v [b [hb hxu]] [c [hc hyv]].
      have [hbc|hcb] := hchain b c hb hc.
      + exact: (svalP c).2 x y u v (hbc x u hxu) hyv.
      + exact: (svalP b).2 x y u v hxu (hcb y v hyv).
  exists (exist nonexpanding_graph_extension_property G hG)=> b hb x y hxy.
  by exists b.
- have hbase : nonexpanding_graph_extension_property original_nonexpanding_graph.
    split; first by [].
    exact: original_nonexpanding_graph_laws.
  exists (exist nonexpanding_graph_extension_property original_nonexpanding_graph hbase)=> b hb.
  exfalso; apply: hempty; by exists b.
Qed.

(** Source for [nonexpanding_total_extension_exists]: direct
    maximality proof of global extension at bound one
    in 2.10.43, p. 201. A missing point would
    admit a strictly larger nonexpanding graph, so
    the maximal graph is total. This private witness
    is used only by later construction and sealing modules. *)
Theorem nonexpanding_total_extension_exists : exists g : X -> Y, is_kirszbraun_extension S f g 1.
Proof.
pose rel (a b : T) := `[< nonexpanding_graph_extension_inclusion a b >].
have hchain (F : set T) : total_on F rel -> exists b : T, forall a, F a -> rel a b.
  move=> hF.
  have hF' : total_on F nonexpanding_graph_extension_inclusion.
    by move=> a b ha hb; case: (hF a b ha hb)=> /asboolP hh; [left|right].
  have [b hb] := nonexpanding_graph_chain_upper hF'.
  exists b=> a ha; apply/asboolP; exact: hb a ha.
have [a hmax'] := @Zorn T rel (fun a=>asboolT (@nonexpanding_graph_extension_refl a))
  (fun a b c hab hbc=>asboolT (nonexpanding_graph_extension_trans (asboolW hab) (asboolW hbc)))
  (fun a b hab hba=>nonexpanding_graph_extension_antisym (asboolW hab) (asboolW hba)) hchain.
have hmax b : nonexpanding_graph_extension_inclusion a b -> b=a by move=> /asboolP /hmax'.
have htotal x : exists y, sval a x y.
  apply: contrapT=> hnot.
  have [y hy] := @kirszbraun_graph_one_point_extension R m n (sval a) x (svalP a).2 hnot.
  have hG : nonexpanding_graph_extension_property (metric_graph_adjoin_value (sval a) x y).
    split=> // z w hzw; left; exact: (svalP a).1 z w hzw.
  pose b : T := exist nonexpanding_graph_extension_property _ hG.
  have hab : nonexpanding_graph_extension_inclusion a b by move=> z w hzw; left.
  have he := hmax b hab.
  have hb : sval b x y by right; split.
  rewrite he in hb; apply: hnot; by exists y.
have [g hg] := @nonexpanding_graph_representative_exists R
  [the metricType R of X] [the metricType R of Y] (sval a) 0 (svalP a).2.
exists g; constructor.
- move=> x hx; exact: hg x (f x) ((svalP a).1 x (f x) (conj hx erefl)).
- split; first exact: ler01.
  move=> x y _ _; have [u hu] := htotal x; have [v hv] := htotal y.
  rewrite (hg x u hu) (hg y v hv) mul1r.
  exact: (svalP a).2 x y u v hu hv.
Qed.
End Extension.
