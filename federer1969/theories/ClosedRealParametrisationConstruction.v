(** Federer (1969), 2.2.10, p. 66: construct a closed subset of N with a
    continuous bijection onto R, using 2.2.9 and the cylinders of 2.2.6. The
    first cylinder maps to Gamma; one point in each selected other cylinder
    accounts for the countable complement. Constant extensions on those
    cylinders give continuity on all of N. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceCylinders
  SequenceCylinderHomeomorphism SequenceCylindricalPasting HomeomorphismOnto
  RealMetricBackground RealSequenceBorelEmbedding ClosedSequenceBijectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_real_sequence_bijection_exists]: supporting
    closed-domain bijection in Federer 2.2.10, p. 66. The constructed map
    extends continuously to the whole sequence space, a strengthening
    obtained by making it constant on each noninitial cylinder. *)
Theorem closed_real_sequence_bijection_exists (R : realType) :
  exists (B : set (positive_sequence_space R))
    (psi : positive_sequence_space R -> real_line_metric R),
    is_closed_sequence_bijection B psi.
Proof.
have [G [g [hG [hcnt hg]]]] := @real_sequence_borel_embedding_countable_complement R.
pose D := ~` G.
have [enc henc] := elimT (@countable_injP (real_line_metric R) D) hcnt.
pose code i := exists x, D x /\ enc x = i.
have hd i : exists x : real_line_metric R, code i -> D x /\ enc x = i.
  case: (pselect (code i))=> [[x hx]|hn].
  - exists x; by move=> _.
  - exists 0; by move=> h; exfalso; exact: hn h.
pose dec i := projT1 (cid (hd i)).
have hdec i : code i -> D (dec i) /\ enc (dec i) = i := projT2 (cid (hd i)).
have hcancel x : D x -> dec (enc x) = x.
  move=> hx; have hi : code (enc x) by exists x.
  have [hdx he] := hdec (enc x) hi.
  apply: henc; try by rewrite inE.
  exact he.
pose n0 := @positive_sequence_default R.
pose point i := @positive_sequence_prepend R i.+1 n0.
pose B := positive_sequence_cylinder 0%N `|` (point @` [set i | code i]).
pose patch j (n : positive_sequence_space R) :=
  if j is i.+1 then dec i else g (positive_sequence_tail n).
pose psi := positive_sequence_cylindrical_paste patch.
have hpsi0 n : positive_sequence_cylinder 0%N n -> psi n = g (positive_sequence_tail n).
  move=> hn; exact: (@positive_sequence_cylindrical_pasteE R _ patch 0%N n hn).
have hpsiS i n : positive_sequence_cylinder i.+1 n -> psi n = dec i.
  move=> hn; exact: (@positive_sequence_cylindrical_pasteE R _ patch i.+1 n hn).
have hpoint i : positive_sequence_cylinder i.+1 (point i).
  exact: positive_sequence_prepend_head.
have hB0 : B `&` positive_sequence_cylinder 0%N = positive_sequence_cylinder 0%N.
  apply/seteqP; split; first by move=> n [_ hn].
  by move=> n hn; split=> //; left.
have hBS i : B `&` positive_sequence_cylinder i.+1 =
    [set n | code i /\ n = point i].
  apply/seteqP; split.
  - move=> n [[hn0|[j hj <-]] hn].
    + have h := eq_trans (esym hn0) hn; discriminate h.
    + have hij : j = i.
        have h := positive_sequence_prepend_head j.+1 n0.
        change (positive_sequence_coordinates (point j) 0%N = j.+1) in h.
        have hs := eq_trans (esym h) hn; by case: hs.
      subst j; by split.
  - move=> n [hi ->]; split; last exact: hpoint.
    right; by exists i.
have hclosed : closed B.
  apply: positive_sequence_cylinderwise_closed=> j; case: j=> [|i].
  - rewrite hB0; exact: positive_sequence_cylinder_closed.
  - rewrite hBS; case: (pselect (code i))=> hi.
    + have he : [set n | code i /\ n = point i] = [set point i].
        apply/seteqP; split; [by move=> n [_ ->]|by move=> n ->; split].
      rewrite he; apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
    + have he : [set n | code i /\ n = point i] = set0.
        apply/seteqP; split; [by move=> n [h _]; exact: hi h|by move=> n []].
      rewrite he; exact: closed0.
have hcontinuous : continuous psi.
  apply: positive_sequence_cylindrical_paste_continuous=> j; case: j=> [|i].
  - move=> n; exact: continuous_comp (@positive_sequence_tail_continuous R n)
      (@homeomorphism_onto_continuous _ _ G g hg (positive_sequence_tail n)).
  - exact: cst_continuous.
have hGvalue n : G (g n).
  rewrite -(homeomorphism_onto_image hg); by exists n.
have hDvalue i : code i -> D (dec i) by move=> hi; exact: (hdec i hi).1.
have hinj : forall m n, B m -> B n -> psi m = psi n -> m = n.
  move=> m n [hm|[i hi <-]] [hn|[j hj <-]] heq.
  - rewrite (hpsi0 m hm) (hpsi0 n hn) in heq.
    have ht := homeomorphism_onto_injective hg heq.
    rewrite -(positive_sequence_prepend_tail hm) -(positive_sequence_prepend_tail hn) ht; by [].
  - rewrite (hpsi0 m hm) (hpsiS j (point j) (hpoint j)) in heq.
    exfalso; apply: (hDvalue j hj); rewrite -heq; exact: hGvalue.
  - rewrite (hpsiS i (point i) (hpoint i)) (hpsi0 n hn) in heq.
    exfalso; apply: (hDvalue i hi); rewrite heq; exact: hGvalue.
  - rewrite (hpsiS i (point i) (hpoint i)) (hpsiS j (point j) (hpoint j)) in heq.
    have h := congr1 enc heq; rewrite (hdec i hi).2 (hdec j hj).2 in h; by rewrite h.
have hsurj : psi @` B = setT.
  apply/seteqP; split; first by move=> x _.
  move=> x _; case: (pselect (G x))=> [hx|hx].
  - rewrite -(homeomorphism_onto_image hg) in hx; have [n _ hn] := hx.
    exists (@positive_sequence_prepend R 0%N n).
    + left; exact: positive_sequence_prepend_head.
    + rewrite hpsi0; last exact: positive_sequence_prepend_head.
      by rewrite positive_sequence_tail_prepend.
  - exists (point (enc x)).
    + right; exists (enc x)=> //; by exists x.
    + rewrite (hpsiS _ _ (hpoint _)); exact: hcancel hx.
exists B, psi; constructor=> //.
Qed.
