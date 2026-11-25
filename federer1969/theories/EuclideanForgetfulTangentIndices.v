(** Federer (1969), 3.2.28(3), p. 266:
    match every target tangent basis vector with its
    unique nonzero source basis direction. The omitted
    directions are precisely b_m,j. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import EuclideanSkewIndexCardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [euclidean_skew_index_lift]: lift the
    c_ij indices to a_ij for i<j<m,
    Federer 3.2.28(3), p. 266. *)
Definition euclidean_skew_index_lift k (p:euclidean_skew_indices k):euclidean_skew_indices k.+1.
Proof.
exists (lift ord_max (val p).1,lift ord_max (val p).2).
change (is_true ((lift ord_max (val p).1:nat)<(lift ord_max (val p).2:nat))).
by rewrite !lift_max; exact:valP p.
Defined.

(** Source for [euclidean_skew_index_last]: the source
    a_i,m indices corresponding to target d_i,m,
    Federer 3.2.28(3), p. 266. *)
Definition euclidean_skew_index_last k (i:'I_k):euclidean_skew_indices k.+1.
Proof.
exists (lift ord_max i,ord_max).
change (is_true ((lift ord_max i:nat)<k)).
by rewrite lift_max; exact:ltn_ord i.
Defined.

(** Source for [euclidean_skew_index_lift_injective]:
    different c_ij give different a_ij directions,
    supporting the diagonal calculation in Federer
    3.2.28(3), p. 266. *)
Lemma euclidean_skew_index_lift_injective k:injective (@euclidean_skew_index_lift k).
Proof.
move=>p q h; have hh:=congr1 val h.
change ((lift ord_max (val p).1,lift ord_max (val p).2)=
  (lift ord_max (val q).1,lift ord_max (val q).2)) in hh.
apply:val_inj; apply/eqP; rewrite -pair_eqE /=; apply/andP; split; apply/eqP.
- exact:lift_inj (congr1 fst hh).
- exact:lift_inj (congr1 snd hh).
Qed.

(** Source for [euclidean_skew_index_last_injective]:
    different d_i,m give different a_i,m directions,
    supporting Federer 3.2.28(3), p. 266. *)
Lemma euclidean_skew_index_last_injective k:injective (@euclidean_skew_index_last k).
Proof.
move=>i j h; have hh:=congr1 (fun p:euclidean_skew_indices k.+1=>(val p).1) h.
exact:lift_inj hh.
Qed.

(** Source for [euclidean_skew_lift_last_disjoint]: the
    i<j<m and i<j=m skew families are disjoint,
    supporting the diagonal differential in Federer
    3.2.28(3), p. 266. *)
Lemma euclidean_skew_lift_last_disjoint k (p:euclidean_skew_indices k) (i:'I_k):
  euclidean_skew_index_lift p!=euclidean_skew_index_last i.
Proof.
apply/eqP=>h.
have hh:=congr1 (fun p:euclidean_skew_indices k.+1=>(val p).2) h.
change (lift ord_max (val p).2=ord_max) in hh.
by have:=lift_eqF ord_max (val p).2; rewrite hh eqxx.
Qed.

(** Source for [euclidean_forgetful_tangent_index]: the
    three nonzero cases of the displayed DS basis
    formulas, Federer 3.2.28(3), p. 266. The
    last target normal index represents g(e_m). *)
Definition euclidean_forgetful_tangent_index k r
    (j:((euclidean_skew_indices k)+('I_k*'I_r.+1))%type):
    ((euclidean_skew_indices k.+1)+('I_k.+1*'I_r))%type:=
  match j with
  | inl p=>inl (euclidean_skew_index_lift p)
  | inr (i,l)=>match unlift ord_max l with
    | Some a=>inr (lift ord_max i,a)
    | None=>inl (euclidean_skew_index_last i)
    end
  end.

(** Source for [euclidean_forgetful_tangent_index_injective]:
    the nonzero differential coefficients occupy distinct
    source directions, Federer 3.2.28(3), p. 266.
    This proves the needed rectangular diagonal indexing,
    including empty skew and normal index families. *)
Theorem euclidean_forgetful_tangent_index_injective k r:
  injective (@euclidean_forgetful_tangent_index k r).
Proof.
move=>[p|[i l]] [q|[j t]].
- move=>h.
  have he:euclidean_skew_index_lift p=euclidean_skew_index_lift q:=inl_inj h.
  by rewrite (euclidean_skew_index_lift_injective he).
- case:(unliftP ord_max t)=>[a ->|->]; rewrite /euclidean_forgetful_tangent_index ?liftK ?unlift_none.
  + by [].
  + move=>h.
    have he:euclidean_skew_index_lift p=euclidean_skew_index_last j:=inl_inj h.
    by move: (euclidean_skew_lift_last_disjoint p j); rewrite he eqxx.
- case:(unliftP ord_max l)=>[a ->|->]; rewrite /euclidean_forgetful_tangent_index ?liftK ?unlift_none.
  + by [].
  + move=>h.
    have he:euclidean_skew_index_last i=euclidean_skew_index_lift q:=inl_inj h.
    by move: (euclidean_skew_lift_last_disjoint q i); rewrite he eqxx.
- case:(unliftP ord_max l)=>[a ->|->];
    case:(unliftP ord_max t)=>[b ->|->];
    rewrite /euclidean_forgetful_tangent_index ?liftK ?unlift_none.
  + move=>h.
    have he:(lift ord_max i,a)=(lift ord_max j,b):=inr_inj h.
    have hij:i=j:=lift_inj (congr1 fst he).
    have hab:a=b:=congr1 snd he.
    by rewrite hij hab.
  + by [].
  + by [].
  + move=>h.
    have he:euclidean_skew_index_last i=euclidean_skew_index_last j:=inl_inj h.
    have hij:i=j:=euclidean_skew_index_last_injective he.
    by rewrite hij.
Qed.

(** Source for [euclidean_forgetful_tangent_index_exhaustion]:
    every source basis direction either has one of
    the three nonzero images or is b_m,j,
    Federer 3.2.28(3), p. 266. The
    alternative is proved from the strict pair indices. *)
Theorem euclidean_forgetful_tangent_index_exhaustion k r
    (i:((euclidean_skew_indices k.+1)+('I_k.+1*'I_r))%type):
  (exists j,i=euclidean_forgetful_tangent_index j) \/
    (exists a,i=inr (ord_max,a)).
Proof.
case:i=>[p|[i a]].
- have hOrder:=valP p.
  case:(unliftP ord_max (val p).1)=>[i hi|hi].
  + case:(unliftP ord_max (val p).2)=>[j hj|hj].
    * have hij:(i<j)%N.
        change (is_true ((val p).1<(val p).2)%N) in hOrder.
        by rewrite hi hj !lift_max in hOrder.
      pose q:euclidean_skew_indices k:=Sub (i,j) hij.
      left; exists (inl q); congr inl; apply:val_inj.
      apply/eqP; rewrite -pair_eqE /=; apply/andP; split; apply/eqP; [exact hi|exact hj].
    * left; exists (inr (i,ord_max)); rewrite /euclidean_forgetful_tangent_index unlift_none.
      congr inl; apply:val_inj.
      apply/eqP; rewrite -pair_eqE /=; apply/andP; split; apply/eqP; [exact hi|exact hj].
  + exfalso.
    have hP2:((val p).2<=k)%N by rewrite -ltnS; exact:ltn_ord.
    change (is_true ((val p).1<(val p).2)%N) in hOrder.
    rewrite hi /= ltnNge in hOrder.
    by move/negP:hOrder; apply.
- case:(unliftP ord_max i)=>[j ->|->].
  + left; exists (inr (j,lift ord_max a)).
    by rewrite /euclidean_forgetful_tangent_index liftK.
  + right; by exists a.
Qed.

(** Source for [euclidean_forgetful_tangent_index_kernel_disjoint]:
    the nonzero-image directions are distinct from every
    b_m,j kernel direction, Federer 3.2.28(3),
    p. 266. This also proves the zero coefficient
    comparisons used in the rectangular Jacobian matrix. *)
Theorem euclidean_forgetful_tangent_index_kernel_disjoint k r
    (j:((euclidean_skew_indices k)+('I_k*'I_r.+1))%type) a:
  euclidean_forgetful_tangent_index j!=inr (ord_max,a).
Proof.
case:j=>[p|[i l]]; first by [].
case:(unliftP ord_max l)=>[b ->|->];
  rewrite /euclidean_forgetful_tangent_index ?liftK ?unlift_none; last by [].
apply/eqP=>h; have he:(lift ord_max i,b)=(ord_max,a):=inr_inj h.
have hf:lift ord_max i=ord_max:=congr1 fst he.
by have:=lift_eqF ord_max i; rewrite hf eqxx.
Qed.
