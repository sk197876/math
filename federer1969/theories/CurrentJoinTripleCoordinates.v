(** Federer (1969), 4.1.11, p. 365: express the
    actual source domain as its original three factors.
    The maps are compositions of the preceding opaque
    Cartesian-domain identifications, not new coordinate constructions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap EuclideanBlockCoordinates
  CurrentDomain CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws
  CurrentJoinDomain CurrentJoinRawCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentJoinTripleCoordinates.
Variable R:realType.
Variable n:nat.
Local Notation Full := (fun _:R_n R n=>True).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation XT := (current_domain R n Full).
Local Notation TT := (current_domain R 1%N Time).
Local Notation CT := (current_domain R (n+(1+n))%N (@current_join_domain R n)).
Local Notation J := (@CartesianCurrentDomain.join R n (1+n)%N Full TimeSpace).
Local Notation D := (@CartesianCurrentDomain.split R n (1+n)%N Full TimeSpace).
Local Notation K := (@CartesianCurrentDomain.join R 1%N n Time Full).
Local Notation E := (@CartesianCurrentDomain.split R 1%N n Time Full).

(** Source for [current_join_triple_point]: the original
    point (x,t,y) on the actual ordered source domain,
    supporting the triple integral in Federer 4.1.11, p. 365. *)
Definition current_join_triple_point (u:XT*(TT*XT)):CT:=J (u.1,K u.2).

(** Source for [current_join_triple_split]: the original
    three factor points recovered by the preceding opaque
    block inverses, supporting Federer 4.1.11, p. 365. *)
Definition current_join_triple_split (z:CT):XT*(TT*XT):=((D z).1,E (D z).2).

(** Source for [current_join_triple_point_split]: splitting
    the actual ordered point recovers all three original
    points, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_triple_point_split:cancel current_join_triple_point current_join_triple_split.
Proof.
move=>u;rewrite /current_join_triple_point /current_join_triple_split
  !current_cartesian_domain_join_split.
by case:u.
Qed.

(** Source for [current_join_triple_split_point]: joining
    the three recovered original points recovers the same
    source point, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_triple_split_point:cancel current_join_triple_split current_join_triple_point.
Proof.
move=>z;rewrite /current_join_triple_point /current_join_triple_split
  !current_cartesian_domain_split_join.
change (J ((D z).1,(D z).2)=z).
rewrite -surjective_pairing.
exact:current_cartesian_domain_split_join.
Qed.

(** Source for [current_join_triple_point_coordinates]: the
    actual x, time and y points of the source are the
    three original factor points, supporting the literal
    partial integrands in Federer 4.1.11, p. 365. *)
Lemma current_join_triple_point_coordinates u:
  @current_join_first_point R n (current_join_triple_point u)=u.1 /\
  @current_join_time_point R n (current_join_triple_point u)=u.2.1 /\
  @current_join_last_point R n (current_join_triple_point u)=u.2.2.
Proof.
by rewrite /current_join_first_point /current_join_time_point /current_join_last_point
  /current_join_triple_point !current_cartesian_domain_join_split.
Qed.

(** Source for [current_join_triple_point_value]: the actual
    source point has the original nested Euclidean block
    value, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_triple_point_value u:
  set_val (current_join_triple_point u)=@euclidean_block_join R n (1+n)%N
    (set_val u.1,@euclidean_block_join R 1%N n (set_val u.2.1,set_val u.2.2)).
Proof.
by rewrite /current_join_triple_point !current_cartesian_domain_join_value.
Qed.
End CurrentJoinTripleCoordinates.
