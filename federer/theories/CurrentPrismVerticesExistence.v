(** Federer (1969), 4.1.11, p. 366: prove
    existence of the independently specified original
    prism vertex families. The recursive witness serves
    this existence proof only and is sealed downstream. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Biorthogonal OrientedSimplexCurrentUP CurrentPrismVerticesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CurrentPrismVerticesExistence.
Variables X Y:Type.
Variables A B:X->Y.

(** Source for [current_prism_vertices_witness]: an
    ordered vertex witness for the two ranges in the
    original prism formula of Federer 4.1.11, p. 366.
    Only existence uses this recursive construction. *)
Fixpoint current_prism_vertices_witness m (v:'I_(m.+1)->X)
    (k:'I_(m.+1)) {struct m}:'I_(m.+2)->Y.
Proof.
destruct m as[|m].
- exact:(ordinal_cons (A (v ord0)) (fun _:'I_1=>B (v ord0))).
- refine(ordinal_cons (A (v ord0)) _).
  destruct(unlift ord0 k) as[p|].
  + exact:(@current_prism_vertices_witness m (current_simplex_tail v) p).
  + exact:(fun r=>B (v r)).
Defined.

(** Source for [current_prism_vertices_witness_lower]:
    the initial vertices have their original A values,
    supporting the existence assertion for Federer
    4.1.11, p. 366. *)
Lemma current_prism_vertices_witness_lower m (v:'I_(m.+1)->X)
    (k r:'I_(m.+1)):
  (r<=k)%N->@current_prism_vertices_witness m v k
    (widen_ord (leqnSn m.+1) r)=A (v r).
Proof.
elim:m v k r=>[|m ih] v k r hr.
- have hk:k=ord0:=ord1 k;have hR:r=ord0:=ord1 r.
  by rewrite hk hR current_prism_widen_zero /current_prism_vertices_witness ordinal_cons0.
- case:(unliftP ord0 k) hr=>[p ->|->] hr;case:(unliftP ord0 r) hr=>[q ->|->] hr.
  + move:hr;rewrite !lift0 ltnS=>hr.
    rewrite /current_prism_vertices_witness liftK current_prism_widen_lift ordinal_consS.
    exact:(ih (current_simplex_tail v) p q hr).
  + by rewrite /current_prism_vertices_witness liftK current_prism_widen_zero ordinal_cons0.
  + by move:hr;rewrite !lift0 /=.
  + by rewrite /current_prism_vertices_witness unlift_none current_prism_widen_zero ordinal_cons0.
Qed.

(** Source for [current_prism_vertices_witness_upper]:
    the remaining vertices have their original B values,
    supporting the existence assertion for Federer
    4.1.11, p. 366. *)
Lemma current_prism_vertices_witness_upper m (v:'I_(m.+1)->X)
    (k r:'I_(m.+1)):
  (k<=r)%N->@current_prism_vertices_witness m v k (lift ord0 r)=B (v r).
Proof.
elim:m v k r=>[|m ih] v k r hr.
- have hk:k=ord0:=ord1 k;have hR:r=ord0:=ord1 r.
  by rewrite hk hR /current_prism_vertices_witness ordinal_consS.
- case:(unliftP ord0 k) hr=>[p ->|->] hr.
  + case:(unliftP ord0 r) hr=>[q ->|->] hr.
    * move:hr;rewrite !lift0 ltnS=>hr.
      rewrite /current_prism_vertices_witness liftK ordinal_consS.
      exact:(ih (current_simplex_tail v) p q hr).
    * by move:hr;rewrite !lift0 /=.
  + by rewrite /current_prism_vertices_witness unlift_none ordinal_consS.
Qed.

(** Source for [current_prism_vertices_exists]: the original
    ordered vertex families exist for all prism dimensions
    and endpoint maps, Federer 4.1.11, p. 366. No
    nondegeneracy, current or boundary premise is required. *)
Theorem current_prism_vertices_exists:
  exists P:forall m:nat,('I_(m.+1)->X)->'I_(m.+1)->'I_(m.+2)->Y,
    is_current_prism_vertices A B P.
Proof.
exists current_prism_vertices_witness;split.
- exact:current_prism_vertices_witness_lower.
- exact:current_prism_vertices_witness_upper.
Qed.
End CurrentPrismVerticesExistence.
