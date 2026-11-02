(** Federer (1969), 2.2.9, p. 65, the initial interval level for X=R. An
    evenly spaced integer grid supplies the whole-line level; its omitted
    points form a countable grid. Later bounded levels use the separate
    interval refinement. Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals
  CountablyInfiniteEnumeration IntervalRefinementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_root_interval_refinement_exists]: supporting
    first interval level for Federer 2.2.9, p. 65: open
    intervals of length e/2 have disjoint interiors and cover R
    except for their integer-grid endpoints. The grid is enumerated
    bijectively, preserving distinctness of all children. *)
Theorem real_root_interval_refinement_exists (R : realType) (e : R) :
  0 < e -> exists F,
    is_real_interval_refinement (@setT (real_line_metric R)) e F.
Proof.
move=> he; pose r := e/2.
have hr : 0 < r by rewrite /r divr_gt0 // ltr0n.
have hr0 : r != 0 by rewrite (gt_eqF hr).
have hre : r < e.
  by rewrite /r ltr_pdivrMr ?ltr0n // -{1}[e]mulr1 (ltr_pM2l he) ltr1n.
pose A (z : int) := (z%:~R * r : R).
pose B (z : int) := ((z+1)%:~R * r : R).
have hgap z : B z - A z = r.
  by rewrite /B /A intrD /= mulrDl mul1r addrAC subrr add0r.
have hord z : A z < B z by rewrite -subr_gt0 hgap.
have hdis i j : i <> j -> real_open_interval (A i) (B i) `&`
    real_open_interval (A j) (B j) = set0.
  move=> hij; case: (ltgtP i j)=> h.
  - apply: real_open_intervals_ordered_disjoint.
    by rewrite /B /A (ler_pM2r hr) ler_int lezD1.
  - rewrite setIC; apply: real_open_intervals_ordered_disjoint.
    by rewrite /B /A (ler_pM2r hr) ler_int lezD1.
  - exfalso; exact: hij h.
have hcover (x : real_line_metric R) : ~ (A @` setT) x ->
    exists z, real_open_interval (A z) (B z) x.
  move=> hn; pose z := Num.floor (x/r).
  have hlo : A z <= x.
    rewrite /A -(ler_pdivlMr _ _ hr) /z -RfloorE; exact: Rfloor_le.
  have hhi : x < B z.
    rewrite /B -(ltr_pdivrMr _ _ hr) intrD /= /z -RfloorE.
    exact: lt_succ_Rfloor.
  have hstrict : A z < x.
    rewrite lt_neqAle hlo andbT; apply/negP=> /eqP heq; apply: hn.
    by exists z.
  exists z; by split.
have hi : injective Posz by move=> i j; case.
have hcnt : countable (@setT int) by exact: countableP.
have [encode [decode [henc hdec]]] := countably_infinite_enumeration hcnt hi.
pose F n := (A (decode n), B (decode n)).
exists F; constructor.
- move=> n; exact: hord.
- by move=> n x _.
- move=> n; rewrite /F /= hgap; exact hre.
- move=> i j hij; apply: hdis.
  move=> h; apply: hij; have hh := congr1 encode h; by rewrite !hdec in hh.
- have hc : countable (A @` setT).
    apply: sub_countable (card_image_le _ _) _; exact: countableP.
  apply: sub_countable _ hc; apply: subset_card_le=> x [_ hn].
  apply: contrapT=> hnot; apply: hn; have [z hz] := hcover x hnot.
  exists (encode z)=> //; by rewrite /F henc.
Qed.
