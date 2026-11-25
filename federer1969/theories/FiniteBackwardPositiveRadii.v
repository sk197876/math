(** Federer (1969), 3.4.8(11), p. 334:
    choose the positive prefix radii successively
    from epsilon_n down to epsilon_m. Each
    preceding radius meets the already proved local
    coefficient bound for the next radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_backward_positive_radii]:
    finite backward choice of the original
    neighbourhood radii, 3.4.8(11), p. 334.
    The property is supplied independently; the
    sequence is only a local existence witness. *)
Theorem finite_backward_positive_radii (R:realType) (step:nat->R->R->Prop):
  (forall j r,0<r ->exists s:R,0<s /\ step j r s) ->
  forall n r,0<r ->exists epsilon:nat->R,
    epsilon n = r /\
    (forall j,(j<=n)%N ->0<epsilon j) /\
    forall j,(j<n)%N ->step j (epsilon j.+1) (epsilon j).
Proof.
move=>hStep;elim=>[|n IH] r hr.
- exists (fun _=>r);split;first by [].
  split;first by move=>j _.
  by move=>j;rewrite ltn0.
- have [s [hs hLastStep]]:=hStep n r hr.
  have [epsilon [hLast [hPositive hSteps]]]:=IH s hs.
  pose epsilon':=fun j=>if j==n.+1 then r else epsilon j.
  exists epsilon';split;first by rewrite /epsilon' eqxx.
  split.
  + move=>j hJN;rewrite /epsilon'.
    case:(eqVneq j n.+1)=>hEqual;first exact:hr.
    apply:hPositive.
    have hLT:(j<n.+1)%N by rewrite ltn_neqAle hEqual hJN.
    by rewrite ltnS in hLT.
  + move=>j hJN.
    case:(eqVneq j n)=>hEqual.
    * subst j.
      have hDifferent:n!=n.+1 by rewrite eqn_leq ltnn andbF.
      rewrite /epsilon' eqxx (negbTE hDifferent) hLast.
      exact:hLastStep.
    * have hJLess:(j<n)%N.
        by rewrite ltn_neqAle hEqual;move:hJN;rewrite ltnS.
      have hFirst:j!=n.+1.
        apply/eqP=>hFalse;subst j;by move:hJN;rewrite ltnn.
      have hNext:j.+1!=n.+1 by rewrite eqSS.
      rewrite /epsilon' (negbTE hFirst) (negbTE hNext).
      exact:hSteps j hJLess.
Qed.
