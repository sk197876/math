(** Federer (1969), 2.5.20, p. 114: separability of K(Y) for a compact
    metric Y is needed to apply 2.5.12. A finite list of basic open sets and
    rational value intervals describes a uniform approximation cell. This is
    supporting general topology, not an additional disintegration
    hypothesis. The narrow num_normedtype import supplies only real
    order-topology background. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology num_normedtype lra.
From Federer Require Import RealMetricBackground CountableOpenBaseUP CompactFiniteCover
  CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactSupportFunctionUP
  UniformFunctionNorm UniformFunctionNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Cells.
Variable R : realType.
Variable Y : topologicalType.
Variable E : lmodType R.
Variable ev : E -> Y -> R.
Variable B : nat -> set Y.

(** Source for [compact_function_interval_cell]: a finite
    rational description of a set of nearby functions, supporting
    separability of K(Y) in Federer 2.5.20, p. 114. *)
Definition compact_function_interval_cell (s : seq (nat*rat*rat)) (v : E) :=
  forall j, j \in s -> forall y, B j.1.1 y -> ratr j.1.2<ev v y<ratr j.2.

(** Source for [compact_function_interval_cell_cover]: every
    continuous function on compact Y belongs to a rational
    cell covering Y with arbitrarily short value intervals.
    This supports separability in Federer 2.5.20, p. 114. *)
Theorem compact_function_interval_cell_cover (hE : is_compact_function_space ev)
    (hB : is_countable_open_base B) (v : E) (d : R) :
  compact (@setT Y) -> 0<d -> exists s : seq (nat*rat*rat),
    (forall y, exists j, j \in s /\ B j.1.1 y) /\
    (forall j, j \in s -> ratr j.2-ratr j.1.2<d) /\ compact_function_interval_cell s v.
Proof.
move=> hY hd.
have hd2 : 0<d/2 by rewrite divr_gt0 // ltr0n.
have hhalves : d/2+d/2=d by rewrite -splitr.
pose J := [the choiceType of ((nat*rat*rat)%type : Type)].
pose D : set J := [set j | (ratr j.2-ratr j.1.2<d) /\
  forall y, B j.1.1 y -> ratr j.1.2<ev v y<ratr j.2].
have hcover : setT `<=` \bigcup_(j in D) B j.1.1.
  move=> y _.
  have hleft : ev v y-d/2<ev v y by lra.
  have hright : ev v y<ev v y+d/2 by lra.
  have [a /andP [ha hay]] := rat_in_itvoo hleft.
  have [b /andP [hyb hb]] := rat_in_itvoo hright.
  pose U : set Y := [set z | ratr a<ev v z<ratr b].
  have hI : open [set t : real_line_metric R | ratr a<t<ratr b].
    have heq : [set t : real_line_metric R | ratr a<t<ratr b]=
        [set t : real_line_metric R | ratr a<t] `&` [set t | t<ratr b].
      by apply/seteqP; split=> t /=; [move/andP|move=> [h1 h2]; apply/andP].
    rewrite heq; exact: openI (@open_gt R (ratr a)) (@open_lt R (ratr b)).
  have hU : open U.
    exact: ((@continuousP Y (real_line_metric R) (ev v)).1
      (compact_function_evaluation_member hE v).1 _ hI).
  have hy : U y by apply/andP; split.
  have [n [hny hn]] := countable_base_refines hB hU hy.
  exists ((n,a),b)=> //; split; last exact: hn.
  change (ratr b-ratr a<d).
  have hwidth : ratr b-ratr a<(ev v y+d/2)-(ev v y-d/2) := ltrB hb ha.
  have he : (ev v y+d/2)-(ev v y-d/2)=d.
    have he' : (ev v y+d/2)-(ev v y-d/2)=d/2+d/2 by lra.
    by rewrite he' -splitr.
  by rewrite he in hwidth.
have [F hF hf] := @compact_open_finite_cover Y J D (fun j => B j.1.1) setT
  hY (fun j _ => countable_base_open hB j.1.1) hcover.
exists (F : seq J); split.
- move=> y; have [j hj hby] := hf y I; by exists j.
- split.
  + move=> j hj; exact: (set_mem (hF j hj)).1.
  + move=> j hj y hy; exact: (set_mem (hF j hj)).2 y hy.
Qed.

(** Source for [compact_function_same_cell_norm_bound]:
    two functions in one covering cell differ uniformly by
    at most the common interval-width bound, supporting the
    countable approximation in Federer 2.5.20, p. 114. *)
Lemma compact_function_same_cell_norm_bound (hE : is_compact_function_space ev)
    (s : seq (nat*rat*rat)) (u v : E) (d : R) :
  0<=d -> (forall y, exists j, j \in s /\ B j.1.1 y) ->
  (forall j, j \in s -> ratr j.2-ratr j.1.2<=d) ->
  compact_function_interval_cell s u -> compact_function_interval_cell s v ->
  compact_function_norm ev (u-v)<=d.
Proof.
move=> hd hcover hwidth hu hv.
apply: (@uniform_function_norm_least R Y (ev (u-v)) _
  (compact_support_uniform_norm_specification (compact_function_evaluation_member hE (u-v))) d hd)=> y.
rewrite (compact_function_evaluation_subtract hE).
have [j [hj hby]] := hcover y.
have /andP [hu1 hu2] := hu j hj y hby.
have /andP [hv1 hv2] := hv j hj y hby.
have hw := hwidth j hj; rewrite ler_norml; apply/andP; split; lra.
Qed.
End Cells.
