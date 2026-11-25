(** General topology supporting Federer (1969), 2.5.15, pp. 108-109: every
    neighbourhood in a product space contains an open set determined by
    finitely many coordinates, and a continuous real function on a compact
    product depends only on countably many coordinates. Federer obtains the
    second fact from the Weierstrass-Stone theorem; here it follows from
    compactness and the finite-coordinate neighbourhoods, a documented
    variation of the proof route. The product topology is the standard one
    of the general-topology background. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap boolp mathcomp_extra
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProductNeighborhoods.
Variable I : choiceType.
Variable Y : I -> topologicalType.

(** Source for [coordinate_cylinders_at]: supporting family of open
    cylinders through a point, each depending on one coordinate, for
    the product topology in Federer 2.5.15, p. 108. *)
Definition coordinate_cylinders_at (x : prod_topology Y) : set (set (prod_topology Y)) :=
  [set S | exists i (O : set (Y i)), open O /\ O (x i) /\ S = [set y : prod_topology Y | O (y i)]].

(** Source for [coordinate_cylinder_open]: supporting openness of a
    one-coordinate cylinder, by continuity of the projection, for
    Federer 2.5.15, p. 108. *)
Lemma coordinate_cylinder_open (i : I) (O : set (Y i)) :
  open O -> open [set y : prod_topology Y | O (y i)].
Proof.
move=> hO; have := @open_comp (prod_topology Y) (Y i) (@proj I Y i) O _ hO.
by apply=> y _; exact: proj_continuous.
Qed.

(** Source for [fset_bigcap_open]: supporting openness of a finite
    intersection of open sets, Federer 2.5.15, p. 108. *)
Lemma fset_bigcap_open (T : topologicalType) (K : choiceType) (D : {fset K}) (F : K -> set T) :
  (forall k, k \in D -> open (F k)) -> open (\bigcap_(k in [set` D]) F k).
Proof.
move=> hF; rewrite bigcap_fset big_seq.
by apply: big_ind; [exact: openT|exact: openI|exact: hF].
Qed.

(** Source for [prod_nbhs_finitely_determined]: supporting neighbourhood
    structure of the product topology for Federer 2.5.15, p. 108: a
    neighbourhood of x contains an open set through x determined by finitely
    many coordinates. The proof uses finite intersections of basic
    neighbourhoods. *)
Theorem prod_nbhs_finitely_determined (x : prod_topology Y) (U : set (prod_topology Y)) :
  nbhs x U -> exists W, open W /\ W x /\ W `<=` U /\
    exists F : {fset I}, forall y z, (forall i, i \in F -> y i = z i) -> W y -> W z.
Proof.
move=> hU.
case: (pselect (exists i : I, True))=> [[i0 _]|hempty]; last first.
  exists setT; split; first exact: openT.
  split=> //; split; last by exists fset0.
  move=> y _; have -> : y = x by apply: functional_extensionality_dep=> i; case: hempty; exists i.
  exact: nbhs_singleton hU.
pose C := coordinate_cylinders_at x.
pose G := filter_from [set W | finI_from C id W /\ W x] id.
have hG : Filter G.
  apply: filter_from_filter.
  - exists setT; split=> //.
    exists fset0; first by move=> W; rewrite inE.
    by rewrite set_fset0 bigcap_set0.
  - move=> A D [hA hxA] [hD hxD]; exists (A `&` D); last by move=> y hy.
    by split; [exact: finI_fromI hA hD|split].
have hc : G --> (x : prod_topology Y).
  apply/cvg_sup=> i V; rewrite (@nbhsE (initial_topology (fun y : prod_topology Y => y i))).
  move=> [W [[O hO <-] hxi] hWV].
  exists [set y : prod_topology Y | O (y i)]; last by move=> y hy; exact: hWV.
  split=> //; apply: finI_from1; exists i, O; split=> //; by split.
have hnb : G U by exact: hc U hU.
have [W [[D' hD' hWD] hxW] hWU] := hnb.
pose ci := fun S : set (prod_topology Y) =>
  if pselect (C S) is left h then sval (cid h) else i0.
have hdet : forall S, S \in D' -> exists O : set (Y (ci S)),
    open O /\ S = [set y : prod_topology Y | O (y (ci S))].
  move=> S hS; rewrite /ci; case: pselect=> [h|hn]; last first.
    by case: hn; exact/set_mem/hD'.
  by have [O [hO [_ hSO]]] := svalP (cid h); exists O.
exists W; split.
- rewrite -hWD; apply: fset_bigcap_open=> S hS.
  have [O [hO hSO]] := hdet S hS; rewrite hSO; exact: coordinate_cylinder_open hO.
split=> //; split=> //.
exists [fset ci S | S in D']%fset=> y z hyz; rewrite -hWD=> hy S hS.
have [O [_ hSO]] := hdet S hS.
have hyS : O (y (ci S)) by move: (hy S hS); rewrite {1}hSO.
have hin : ci S \in [fset ci S0 | S0 in D']%fset by apply/imfsetP; exists S.
by rewrite {1}hSO /= -(hyz (ci S) hin).
Qed.

End ProductNeighborhoods.

Section PointedProduct.
Variables (J : choiceType) (Y : ptopologicalType).
(** Source for [constant_product_point]: supporting distinguished
    point of the constant product space, needed by the open-cover
    form of compactness used for Federer 2.5.15, p. 108. *)
Definition constant_product_point : prod_topology (fun _ : J => Y) := fun _ => point.
HB.instance Definition _ := isPointed.Build (prod_topology (fun _ : J => Y)) constant_product_point.
End PointedProduct.

(** Source for [compact_product_continuous_countably_determined]: the
    fact used in Federer 2.5.15, pp. 108-109, that for each f in K(X)
    there is a countable set S of coordinates such that f(x) depends
    only on p_j(x) for j in S. Federer cites the Weierstrass-Stone
    theorem; here compactness gives, for each positive error, a finite
    cover by sets determined by finitely many coordinates. The function
    is then constant on classes of points agreeing on the countable union
    of these finite coordinate sets. *)
Theorem compact_product_continuous_countably_determined (R : realType) (J : choiceType)
    (Y : ptopologicalType) (f : prod_topology (fun _ : J => Y) -> real_line_metric R) :
  compact [set: prod_topology (fun _ : J => Y)] -> continuous f ->
  exists S : set J, countable S /\ forall y z, (forall j, S j -> y j = z j) -> f y = f z.
Proof.
move=> hX hf.
pose e := fun m : nat => (m.+1%:R^-1 : R).
have he : forall m, 0 < e m by move=> m; rewrite invr_gt0 ltr0n.
have hstep : forall m, exists S : set J, countable S /\
    forall y z, (forall j, S j -> y j = z j) -> `|f y - f z| < e m + e m.
  move=> m.
  have hnb : forall x, nbhs x (f @^-1` ball (f x) (e m)).
    by move=> x; apply: (hf x); exact: nbhsx_ballx (he m).
  have hch : forall x, exists W : set (prod_topology (fun _ : J => Y)), exists F : {fset J},
      open W /\ W x /\ W `<=` f @^-1` ball (f x) (e m) /\
      forall y z, (forall j, j \in F -> y j = z j) -> W y -> W z.
    move=> x; have [W [hWo [hWx [hWU [F hF]]]]] := prod_nbhs_finitely_determined (hnb x).
    by exists W, F.
  pose Wf := fun x => sval (cid (hch x)).
  pose Ff := fun x => sval (cid (svalP (cid (hch x)))).
  have hWf : forall x, open (Wf x) /\ Wf x x /\ Wf x `<=` f @^-1` ball (f x) (e m) /\
      forall y z, (forall j, j \in Ff x -> y j = z j) -> Wf x y -> Wf x z.
    by move=> x; exact: svalP (cid (svalP (cid (hch x)))).
  have hcov : cover_compact [set: prod_topology (fun _ : J => Y)] by rewrite -compact_cover.
  have hsub : [set: prod_topology (fun _ : J => Y)] `<=` cover setT Wf.
    by move=> x _; exists x=> //; exact: (hWf x).2.1.
  have [D' _ hD'] := hcov _ setT Wf (fun x _ => (hWf x).1) hsub.
  exists (\bigcup_(x in [set` D']) [set` Ff x]); split.
  - apply: bigcup_countable; first exact: finite_set_countable (finite_fset D').
    by move=> x _; exact: finite_set_countable (finite_fset (Ff x)).
  - move=> y z hyz.
    have [x hxD hyW] := hD' y Logic.I.
    have hzW : Wf x z.
      apply: (hWf x).2.2.2 _ _ _ hyW=> j hj; apply: hyz; by exists x.
    have hy := (hWf x).2.2.1 _ hyW; have hz := (hWf x).2.2.1 _ hzW.
    have := ball_triangle (ball_sym hy) hz.
    by rewrite real_line_ball_distance.
pose Sm := fun m => sval (cid (hstep m)).
exists (\bigcup_m Sm m); split.
- by apply: bigcup_countable=> // m _; exact: (svalP (cid (hstep m))).1.
- move=> y z hyz; apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT leNgt.
  apply/negP=> hpos.
  have h2 : (0 < 2 :> R) by rewrite ltr0n.
  have [m hm] := real_reciprocal_below (divr_gt0 hpos h2).
  have := (svalP (cid (hstep m))).2 y z (fun j hj => hyz j (ex_intro2 _ _ m Logic.I hj)).
  rewrite /e ltNge=> /negP; apply.
  move: hm; rewrite ltr_pdivlMr ?ltr0n // mulr_natr mulr2n=> hm.
  exact: ltW hm.
Qed.
