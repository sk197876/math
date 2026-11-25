(** Supporting fact for Federer (1969), 2.5.17, pp. 110-111: a continuous
    real function is uniformly continuous on a compact segment, so that sup
    {|f(u) - f(v)| : |u - v| <= delta} approaches zero with delta. The proof
    covers the segment by balls of half the continuity radii and takes the
    least half radius of a finite subcover. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology normedtype.
From mathcomp Require Import lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuity_radius_exists]: supporting pointwise
    continuity radius, Federer 2.5.17, p. 111. *)
Lemma continuity_radius_exists (R : realType) (f : R -> R) (x e : R) :
  continuous f -> 0 < e -> exists d, 0 < d /\ forall y, `|x - y| < d -> `|f x - f y| < e.
Proof.
move=> hf he.
have hnb : nbhs x (f @^-1` ball (f x) e) by exact ((cvg_ballP _ _).1 (hf x) e he).
by have [d hd hsub] := (nbhs_ballP _ _).1 hnb; exists d; split.
Qed.

(** Source for [segment_uniform_continuity]: uniform continuity of a
    continuous real function on a segment, the fact behind "approaches
    0 as delta approaches 0" in Federer 2.5.17, p. 111. *)
Theorem segment_uniform_continuity (R : realType) (f : R -> R) (a b e : R) :
  continuous f -> 0 < e ->
  exists d, 0 < d /\ forall x y, a <= x <= b -> a <= y <= b -> `|x - y| < d -> `|f x - f y| < e.
Proof.
move=> hf he.
have he2 : 0 < e / 2 by rewrite divr_gt0 ?ltr0n.
pose rad := fun x : R => sval (cid (continuity_radius_exists x hf he2)).
have hrad : forall x, 0 < rad x /\ forall y, `|x - y| < rad x -> `|f x - f y| < e / 2.
  by move=> x; exact: svalP (cid (continuity_radius_exists x hf he2)).
have hcov : cover_compact `[a, b] by rewrite -compact_cover; exact: segment_compact.
have hsub : `[a, b] `<=` cover `[a, b] (fun x => interior (ball x (rad x / 2))).
  move=> x hx; exists x=> //; apply: nbhsx_ballx.
  by rewrite divr_gt0 // (hrad x).1.
have [D hDsub hD'] := hcov _ `[a, b] (fun x : R => interior (ball x (rad x / 2)))
  (fun (x : R) _ => open_interior _) hsub.
case: (pselect (exists x0, x0 \in D))=> [[x0 hx0]|hempty]; last first.
  exists 1; split=> // x y hx hy _.
  have [x1 hx1 _] := hD' x hx.
  by case: hempty; exists x1.
pose m := \big[Order.min/rad x0 / 2]_(i : D) (rad (val i) / 2).
have hm : 0 < m.
  rewrite /m; apply: (big_ind (fun v : R => 0 < v)); first by rewrite divr_gt0 // (hrad x0).1.
  - by move=> u v hu hv; rewrite lt_min hu hv.
  - by move=> i _; rewrite divr_gt0 // (hrad (val i)).1.
have hmle : forall x, x \in D -> m <= rad x / 2.
  by move=> x hx; have := bigmin_le (rad x0 / 2) [` hx]%fset (fun i : D => rad (val i) / 2).
exists m; split=> // x y hx hy hxy.
have [c hc hxc] := hD' x hx.
have hcD : c \in D := hc.
move: hxc=> /interior_subset; rewrite /ball /= => hxc.
have h1 : `|f c - f x| < e / 2.
  apply: (hrad c).2; apply: lt_le_trans hxc _.
  by have := (hrad c).1; lra.
have h2 : `|f c - f y| < e / 2.
  apply: (hrad c).2; apply: le_lt_trans (ler_distD x _ _) _.
  rewrite (splitr (rad c)); apply: ltrD=> //.
  exact: lt_le_trans hxy (hmle c hcD).
have := ler_distD (f c) (f x) (f y).
rewrite distrC in h1; move=> h3; apply: le_lt_trans h3 _.
by rewrite (splitr e); exact: ltrD h1 h2.
Qed.
