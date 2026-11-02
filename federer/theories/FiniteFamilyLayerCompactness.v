(** Federer (1969), 3.2.39, pp. 275--276: actual
    multiplicity layers of finitely many compact images are compact. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import FiniteFamilyMultiplicity FiniteFamilyLayersUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_family_layers_compact]: compactness of
    the sets S_j defined in Federer 3.2.39, p. 275.
    Recursion on the actual finite index enumeration expresses
    each positive threshold as a union of a previous positive
    threshold and a compact member intersected with a closed
    threshold. The zero threshold is the whole space. This
    proves compactness by finite unions and closed intersections,
    without introducing a powerset of index sets or assuming
    a common containing compact set or a nonempty ambient space. *)
Lemma finite_family_layers_compact (R:realType) (X:metricType R) (I:finType)
    (K:I->set X) (S:'I_(#|I|)->set X):
  (forall i,compact (K i)) ->is_finite_family_layers K S ->forall j,compact (S j).
Proof.
move=>hK hS j.
pose N (s:seq I) (x:X):=count (fun i=>asbool (K i x)) s.
pose T (s:seq I) (k:nat):set X:=[set x|(k<=N s x)%N].
have hCount x:N (enum I) x=finite_family_hit_count K x.
  symmetry; by rewrite /finite_family_hit_count cardE enumT /enum_mem size_filter.
have hZero s:T s 0%N=setT.
  apply/seteqP; split=>x hx; first exact Logic.I.
  exact:leq0n.
have hEmpty k:T [::] k.+1=set0.
  apply/seteqP; split=>[x hx|x []].
  by move:hx; rewrite /T /N /= ltn0.
have hStep i s k:T (i::s) k.+1=T s k.+1 `|` (K i `&` T s k).
  apply/seteqP; split.
  - move=>x hx.
    change (is_true (k.+1<=asbool (K i x)+N s x)%N) in hx.
    case:(asboolP (K i x))=>hKi in hx.
    + right; split=>//; by move:hx; rewrite add1n ltnS.
    + left; by move:hx; rewrite add0n.
  - move=>x [hx|[hKi hx]].
    + change (is_true (k.+1<=asbool (K i x)+N s x)%N).
      case:(asboolP (K i x))=>hKi.
      * rewrite add1n; exact:leq_trans hx (leqnSn (N s x)).
      * by rewrite add0n.
    + change (is_true (k.+1<=asbool (K i x)+N s x)%N).
      have hTrue:asbool (K i x):=asboolT hKi.
      by rewrite hTrue add1n ltnS.
have hClosed s:forall k,closed (T s k).
  elim:s=>[|i s ih] k.
  - case:k=>[|k]; [by rewrite hZero; exact:closedT|by rewrite hEmpty; exact:closed0].
  - case:k=>[|k]; first by rewrite hZero; exact:closedT.
    rewrite hStep; apply:closedU; first exact:ih.
    exact:closedI (compact_closed (@metric_hausdorff R X) (hK i)) (ih k).
have hCompact s k:compact (T s k.+1).
  elim:s=>[|i s ih]; first by rewrite hEmpty; exact:compact0.
  rewrite hStep; apply:compactU; first exact ih.
  exact:compact_closedI (hK i) (hClosed s k).
have hLayer:S j=T (enum I) j.+1.
  apply/seteqP; split=>x hx.
  - have hHit:=(hS j x).1 hx.
    change (is_true (j.+1<=N (enum I) x)%N); by rewrite hCount.
  - apply:(hS j x).2.
    change (is_true (j.+1<=N (enum I) x)%N) in hx.
    by rewrite hCount in hx.
rewrite hLayer; exact:hCompact.
Qed.
